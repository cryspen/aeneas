(** The hax specs producer.

    Hax encodes [#[hax_lib::requires(...)]] / [#[hax_lib::ensures(|r| ...)]]
    annotations as separate "decoration" functions plus [_hax::json] attributes
    that link a real function to its pre/post decorations by UUID. This module
    parses those attributes, and the [produce] producer folds them into
    {!Spec.spec} / {!Spec.proof_obligation} entries (consuming the decoration
    functions). The [_hax::json] attribute payloads are parsed by
    {!HaxAttributes}. *)

open HaxAttributes

let log = Logging.translate_log

(** The item contracts are attached to *)
type parent = Fun of Pure.fun_decl | Method of Pure.trait_method

(** The name of [parent], for messages *)
let parent_name (ctx : TranslateCore.trans_ctx) : parent -> string = function
  | Fun f -> f.name
  | Method m -> TranslateCore.name_to_string ctx m.item_meta.name

(** The LLBC name of [parent] *)
let parent_llbc_name : parent -> Types.name = function
  | Fun f -> f.item_meta.name
  | Method m -> m.item_meta.name

(** The span of [parent] *)
let parent_span : parent -> Meta.span = function
  | Fun f -> f.item_meta.span
  | Method m -> m.item_meta.span

(** The number of inputs of [parent] *)
let parent_arity : parent -> int = function
  | Fun f -> List.length f.signature.inputs
  | Method m -> List.length m.signature.inputs

(** Per-parent accumulator while scanning attributes. *)
type assoc = {
  parent : parent;
  requires_uid : string option;
  ensures_uid : string option;
}

let empty_assoc parent = { parent; requires_uid = None; ensures_uid = None }

(** Update an accumulator with one [AssociatedItem]. Per design we accept at
    most one of each role per fn: extras are logged and ignored. *)
let update_assoc (ctx : TranslateCore.trans_ctx) (role : hax_role)
    (uid : string) (a : assoc) : assoc =
  let warn_extra side =
    [%lwarning
      Printf.sprintf "hax-specs: multiple #[%s] on fn `%s`; ignoring extras"
        side (parent_name ctx a.parent)]
  in
  match role with
  | Requires -> (
      match a.requires_uid with
      | None -> { a with requires_uid = Some uid }
      | Some _ ->
          warn_extra "requires";
          a)
  | Ensures -> (
      match a.ensures_uid with
      | None -> { a with ensures_uid = Some uid }
      | Some _ ->
          warn_extra "ensures";
          a)
  | Other_role -> a

(** The uids referenced by the [AssociatedItem]s among [attributes] *)
let associated_uids (attributes : Charon.Meta.attribute list) : string list =
  List.filter_map
    (fun a ->
      match parse_attr a with
      | Some (Associated_item { uid; _ }) -> Some uid
      | _ -> None)
    attributes

(** Read a hax-annotated crate: emit one [TraitSpec] per local trait and one
    [FunctionSpec] per real fn that carries [AssociatedItem] attribute(s), and
    strip the decoration fns whose bodies have been folded into those specs. *)
let produce (ctx : TranslateCore.trans_ctx)
    (crate : TranslateCore.translated_crate) : TranslateCore.translated_crate =
  let _, fresh_spec_id = Spec.SpecId.fresh_stateful_generator () in
  let _, fresh_proof_id = Spec.ProofId.fresh_stateful_generator () in
  let uid_map : Pure.fun_decl Collections.StringMap.t ref =
    ref Collections.StringMap.empty
  in
  let dec_set : Pure.FunDeclId.Set.t ref = ref Pure.FunDeclId.Set.empty in
  let assoc_map : assoc Pure.FunDeclId.Map.t ref =
    ref Pure.FunDeclId.Map.empty
  in
  (* Pass 1: classify each fun_decl by its [_hax::json] payloads. *)
  List.iter
    (fun (ft : TranslateCore.pure_fun_translation) ->
      let f = ft.f in
      (* The contracts of a default method are also on the trait's method
         entry: we read them from there (pass 2) *)
      let is_default =
        match f.src with
        | TraitDefaultFun _ -> true
        | _ -> false
      in
      List.iter
        (fun a ->
          match parse_attr a with
          | None | Some Other_payload | Some Late_skip -> ()
          | Some (Uid uid) ->
              uid_map := Collections.StringMap.add uid f !uid_map;
              dec_set := Pure.FunDeclId.Set.add f.def_id !dec_set
          | Some (Associated_item _) when is_default -> ()
          | Some (Associated_item { role; uid }) ->
              let cur =
                match Pure.FunDeclId.Map.find_opt f.def_id !assoc_map with
                | Some a -> a
                | None -> empty_assoc (Fun f)
              in
              assoc_map :=
                Pure.FunDeclId.Map.add f.def_id
                  (update_assoc ctx role uid cur)
                  !assoc_map)
        f.item_meta.attr_info.attributes)
    crate.fun_decls;

  (* Pass 2: resolve uids to decoration fns and build [Spec.spec] /
     [Spec.proof_obligation] entries, for the traits then for the fns.

     A decoration fn is reused as a proper function: we rename it to
     [<parent>::<suffix>] and mark it [reducible], so the standard function
     extractor prints it as [@[reducible] def <fn>.pre …] / [… .post …]. Its
     [item_meta.name] is only informative: [ExtractHaxSpecs] derives the
     extracted name from the parent's. The
     whole [Pure.fun_decl] is stashed in the spec (it is stripped from
     [crate.fun_decls] in pass 3, so it isn't also printed among the regular
     functions). *)
  let rename_decoration (parent : parent) (suffix : string)
      (dec : Pure.fun_decl) : Pure.fun_decl =
    let name =
      parent_llbc_name parent
      @ [ Types.PeIdent (suffix, Pure.Disambiguator.zero) ]
    in
    let item_meta = { dec.item_meta with name } in
    {
      dec with
      item_meta;
      name = parent_name ctx parent ^ "." ^ suffix;
      backend_attributes = { reducible = true };
    }
  in
  (* Resolve a decoration uid. Checks the arity. *)
  let lookup_dec (parent : parent) ~(suffix : string) ?(is_post = false)
      (uid : string) : Pure.fun_decl option =
    match Collections.StringMap.find_opt uid !uid_map with
    | None ->
        [%lwarning
          Printf.sprintf
            "hax-specs: fn `%s` references unknown decoration uid %s; skipping \
             that side"
            (parent_name ctx parent) uid];
        None
    | Some dec ->
        let decl = rename_decoration parent suffix dec in
        let expected_arity = parent_arity parent + if is_post then 1 else 0 in
        let actual_arity = List.length decl.signature.inputs in
        if expected_arity = actual_arity then Some decl
        else begin
          [%lwarning
            Printf.sprintf
              "hax-specs: argument count mismatch for `%s.%s` (takes %d, \
               expected %d); dropping this condition"
              (parent_name ctx parent) suffix actual_arity expected_arity];
          None
        end
  in
  let shape = function
    | None -> "absent"
    | Some _ -> "present"
  in
  (* Resolve the pre/post conditions of an accumulator *)
  let lookup_conds (a : assoc) : Pure.fun_decl option * Pure.fun_decl option =
    ( Option.bind a.requires_uid (lookup_dec a.parent ~suffix:"pre"),
      Option.bind a.ensures_uid
        (lookup_dec a.parent ~suffix:"post" ~is_post:true) )
  in
  (* The contracts of the local traits, in the order of the declaration groups
     (parents first). Every local trait gets one, even without annotated
     methods. *)
  let trait_decls =
    Pure.TraitDeclId.Map.of_list
      (List.map (fun (d : Pure.trait_decl) -> (d.def_id, d)) crate.trait_decls)
  in
  let method_spec (m : Pure.trait_method) : HaxSpecs.method_spec option =
    let a =
      List.fold_left
        (fun a attr ->
          match parse_attr attr with
          | Some (Associated_item { role; uid }) -> update_assoc ctx role uid a
          | _ -> a)
        (empty_assoc (Method m)) m.item_meta.attr_info.attributes
    in
    match lookup_conds a with
    | None, None -> None
    | pre, post -> Some { method_id = m.method_id; pre; post }
  in
  let local_trait_decls =
    List.concat_map
      (fun (g : LlbcAst.declaration_group) ->
        match g with
        | TraitDeclGroup g ->
            List.filter_map
              (fun id ->
                match Pure.TraitDeclId.Map.find_opt id trait_decls with
                | Some (d : Pure.trait_decl) when d.item_meta.is_local -> Some d
                | _ -> None)
              (Charon.GAstUtils.g_declaration_group_to_list g)
        | _ -> [])
      (Option.get ctx.crate.declarations)
  in
  let trait_specs =
    List.map
      (fun (d : Pure.trait_decl) : Spec.spec ->
        let methods = List.filter_map method_spec d.methods in
        {
          id = fresh_spec_id ();
          span = Some d.item_meta.span;
          kind = HaxSpec (TraitSpec { trait_decl = d.def_id; methods });
        })
      local_trait_decls
  in

  (* Build the spec (statement of correctness) and the proof obligation that
     discharges it, for one parent fn's accumulated [AssociatedItem]s. *)
  let build_entry (parent_id, a) : (Spec.spec * Spec.proof_obligation) option =
    let pre, post = lookup_conds a in
    if Option.is_none pre && Option.is_none post then None
    else (
      [%ltrace
        Printf.sprintf "hax-specs:   fn=%s pre=%s post=%s"
          (parent_name ctx a.parent) (shape pre) (shape post)];
      let span = Some (parent_span a.parent) in
      (* One [function_spec] payload, shared between the spec and the proof
         obligation that discharges it. *)
      let fspec : HaxSpecs.function_spec = { fn = parent_id; pre; post } in
      let spec : Spec.spec =
        { id = fresh_spec_id (); span; kind = HaxSpec (FunctionSpec fspec) }
      in
      let obligation : Spec.proof_obligation =
        {
          id = fresh_proof_id ();
          span;
          kind = HaxProof (FunctionContract { spec = fspec; proof = Admitted });
        }
      in
      Some (spec, obligation))
  in
  let new_specs, new_obligations =
    Pure.FunDeclId.Map.bindings !assoc_map
    |> List.filter_map build_entry
    |> List.split
  in

  (* Pass 3: strip the decoration fns from [crate.fun_decls]. Those that are
     not consumed are reported: as a warning when no translated item refers to
     them, in the log otherwise (unsupported role such as [decreases], extra
     condition, argument count mismatch) *)
  let referenced =
    Collections.StringSet.of_list
      (List.concat_map
         (fun (ft : TranslateCore.pure_fun_translation) ->
           associated_uids ft.f.item_meta.attr_info.attributes)
         crate.fun_decls
      @ List.concat_map
          (fun (d : Pure.trait_decl) ->
            List.concat_map
              (fun (m : Pure.trait_method) ->
                associated_uids m.item_meta.attr_info.attributes)
              d.methods)
          local_trait_decls)
  in
  (* The decorations stashed in the specs keep their [def_id] *)
  let consumed =
    let conds (s : Spec.spec) : Pure.fun_decl option list =
      match s.kind with
      | HaxSpec (FunctionSpec { pre; post; _ }) -> [ pre; post ]
      | HaxSpec (TraitSpec { methods; _ }) ->
          List.concat_map
            (fun (m : HaxSpecs.method_spec) -> [ m.pre; m.post ])
            methods
    in
    Pure.FunDeclId.Set.of_list
      (List.filter_map
         (Option.map (fun (f : Pure.fun_decl) -> f.def_id))
         (List.concat_map conds (trait_specs @ new_specs)))
  in
  let report_dropped (dec : Pure.fun_decl) =
    if not (Pure.FunDeclId.Set.mem dec.def_id consumed) then
      List.iter
        (fun a ->
          match parse_attr a with
          | Some (Uid uid) ->
              let msg reason =
                Printf.sprintf "hax-specs: dropping the hax decoration `%s`: %s"
                  dec.name reason
              in
              if Collections.StringSet.mem uid referenced then
                [%lwarning msg "unsupported or invalid annotation"]
              else
                [%warn] dec.item_meta.span
                  (msg "it is attached to no translated item")
          | _ -> ())
        dec.item_meta.attr_info.attributes
  in
  let new_fun_decls =
    List.filter
      (fun (ft : TranslateCore.pure_fun_translation) ->
        if Pure.FunDeclId.Set.mem ft.f.def_id !dec_set then (
          report_dropped ft.f;
          false)
        else true)
      crate.fun_decls
  in

  [%linfo
    Printf.sprintf
      "hax-specs: produced %d TraitSpec and %d FunctionSpec entries"
      (List.length trait_specs) (List.length new_specs)];

  {
    crate with
    fun_decls = new_fun_decls;
    specs = crate.specs @ trait_specs @ new_specs;
    proof_obligations = crate.proof_obligations @ new_obligations;
  }
