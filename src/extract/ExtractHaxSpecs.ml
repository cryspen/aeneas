module F = Format

module Helpers = struct
  (** Emit [words] separated by breakable spaces *)
  let emit_words (fmt : F.formatter) (words : string list) : unit =
    List.iteri
      (fun i w ->
        if i > 0 then F.pp_print_space fmt ();
        F.pp_print_string fmt w)
      words

  (** Emit a pre/post condition function declaration. [extract_fun_decl] emits
      its own leading break, so we add no trailing separator here. *)
  let emit_cond (ctx : ExtractBase.extraction_ctx) (fmt : F.formatter)
      (f : Pure.fun_decl) : unit =
    Extract.extract_fun_decl ctx fmt ExtractBase.SingleNonRec false f

  (** Run [k] on its own line inside an [hovbox] *)
  let line (fmt : F.formatter) (k : unit -> unit) : unit =
    F.pp_print_cut fmt ();
    F.pp_open_hovbox fmt 0;
    k ();
    F.pp_close_box fmt ()

  (** Wrap [k] in a Hoare-triple postcondition delimiter [⦃ … ⦄]. *)
  let emit_wp (fmt : F.formatter) (k : unit -> unit) : unit =
    Extract.emit_delim ~add_spaces:false fmt "⦃ " k " ⦄"

  (** Emit a binder [(<name> : <ty>)], with [k] printing [<ty>] *)
  let emit_binder fmt (name : string) (k : unit -> unit) =
    F.pp_print_space fmt ();
    F.pp_open_hovbox fmt 0;
    F.pp_print_string fmt ("(" ^ name);
    F.pp_print_space fmt ();
    F.pp_print_string fmt ":";
    F.pp_print_space fmt ();
    k ();
    F.pp_print_string fmt ")";
    F.pp_close_box fmt ()

  (** Emit [<name> <generics> <args>] — an application head applied to its
      generic and value arguments (caller controls the surrounding box). This is
      for [<fn>.spec], which is synthesized at extraction time and thus has no
      declaration to point at. *)
  let emit_app span ctx fmt explicit generics args (name : string) =
    F.pp_print_string fmt name;
    (* Generic args, matching the head's generic binders. *)
    ExtractTypes.extract_generic_args span ctx fmt Pure.TypeDeclId.Set.empty
      ~explicit:(Some explicit) generics;
    List.iter
      (fun te ->
        F.pp_print_space fmt ();
        Extract.extract_texpr span ctx fmt ~inside:true ~inside_do:false te)
      args

  (** The head of an application of the local function [id] to [generics]. *)
  let fun_head (id : Pure.FunDeclId.id) generics (ty : Pure.ty) : Pure.texpr =
    let id = Pure.FunOrOp (Fun (FromLlbc (FunId (FRegular id), None))) in
    { e = Qualif { id; generics }; ty }

  (** The arguments passed for the input patterns of a function. Unit inputs are
      [_] (see [unit_vars_to_unit]): we pass them as [()]. *)
  let input_args span (inputs : Pure.tpat list) : Pure.texpr list =
    List.map
      (fun (p : Pure.tpat) ->
        match PureUtils.tpat_to_texpr span p with
        | Some e -> e
        | None when p.ty = PureUtils.mk_unit_ty -> PureUtils.mk_unit_texpr
        | None -> [%internal_error] span)
      inputs

  (** The arguments of a method with signature [sg], as fresh variables
      registered in [ctx], named after the inputs of the precondition [pre]. *)
  let method_args span (ctx : ExtractBase.extraction_ctx) fresh_fvar_id
      (sg : Pure.fun_sig) (pre : Pure.fun_decl option) :
      ExtractBase.extraction_ctx * Pure.texpr list =
    let inputs =
      Option.fold ~none:[]
        ~some:(fun (b : Pure.fun_body) -> b.inputs)
        (Option.bind pre (fun (f : Pure.fun_decl) -> f.body))
    in
    let name i =
      match Option.bind (List.nth_opt inputs i) PureUtils.as_opt_pat_bound with
      | Some ({ basename = Some n; _ }, _) -> n
      | _ -> "_"
    in
    List.fold_left_map
      (fun ctx (i, ty) ->
        let id = fresh_fvar_id () in
        let ctx, _ = ExtractBase.ctx_add_var span (name i) id ctx in
        (ctx, ({ e = FVar id; ty } : Pure.texpr)))
      ctx
      (List.mapi (fun i ty -> (i, ty)) sg.inputs)

  (** The instance of the parent clause [c] of the trait [d], from the instance
      [tr] of [d]: the generics of [c] are instantiated for [tr] *)
  let parent_ref (d : Pure.trait_decl) (tr : Pure.trait_ref)
      (c : Pure.trait_param) : Pure.trait_ref =
    let subst =
      PureUtils.make_subst_from_generics_for_trait d.generics tr.trait_id
        tr.trait_decl_ref.decl_generics
    in
    {
      trait_id = ParentClause (tr.trait_id, d.def_id, c.clause_id);
      trait_decl_ref =
        {
          trait_decl_id = c.trait_id;
          decl_generics = PureUtils.generic_args_substitute subst c.generics;
        };
    }

  (** The generics to pass to a pre/post condition [cond], from the [generics]
      of the function it describes. The types and const generics match, but the
      trait clauses may not: for [trait B: A], the conditions of a method of [B]
      have clauses [Self_: A] and [Self_: B], while the method only has
      [Self: B]. We look up each clause of [cond] among the trait refs of
      [generics] and their parent clauses. The clauses of [cond] are written in
      its own type and const generic parameters, while [generics] may use other
      variables (e.g., those of a trait and its method): we substitute them with
      the types and const generics of [generics] before the lookup. *)
  let cond_generics span (ctx : ExtractBase.extraction_ctx)
      (generics : Pure.generic_args) (cond : Pure.fun_decl) : Pure.generic_args
      =
    let rec with_parents (tr : Pure.trait_ref) : Pure.trait_ref list =
      match
        Pure.TraitDeclId.Map.find_opt tr.trait_decl_ref.trait_decl_id
          ctx.trans_trait_decls
      with
      | None -> [ tr ]
      | Some d ->
          tr
          :: List.concat_map
               (fun c -> with_parents (parent_ref d tr c))
               d.parent_clauses
    in
    let available = List.concat_map with_parents generics.trait_refs in
    let params = cond.signature.generics in
    [%cassert] span
      (List.length params.types = List.length generics.types
      && List.length params.const_generics = List.length generics.const_generics
      )
      ("Internal error: the generics of the condition `" ^ cond.name
     ^ "` don't match those it is applied to");
    let subst : PureUtils.subst =
      {
        ty_subst = PureUtils.make_type_subst params.types generics.types;
        cg_subst =
          PureUtils.make_const_generic_subst params.const_generics
            generics.const_generics;
        tr_subst = (fun id -> Clause (Free id));
        tr_self = Self;
      }
    in
    let find (c : Pure.trait_param) : Pure.trait_ref =
      let decl_ref : Pure.trait_decl_ref =
        {
          trait_decl_id = c.trait_id;
          decl_generics = PureUtils.generic_args_substitute subst c.generics;
        }
      in
      match
        List.find_opt
          (fun (tr : Pure.trait_ref) -> tr.trait_decl_ref = decl_ref)
          available
      with
      | Some tr -> tr
      | None ->
          [%craise] span
            "Could not find an instance for a trait clause of a pre/post \
             condition"
    in
    {
      generics with
      trait_refs = List.map find cond.signature.generics.trait_clauses;
    }

  (** The generics of a method of the trait [d] with signature [sg], from the
      instance [self_ref] of [d]: those of the trait, then those of the method,
      as the conditions of the method take them. *)
  let method_generics (d : Pure.trait_decl) (self_ref : Pure.trait_ref)
      (sg : Pure.fun_sig) : Pure.generic_args =
    let trait_args = PureUtils.generic_args_of_params d.generics in
    (* The de Bruijn indices of the method generics are not reliable (see
       {!ExtractBase.origin_from_de_bruijn_var}): we reset them, so that
       {!cond_generics} can compare the trait refs *)
    let reset =
      object
        inherit [_] Pure.map_ty
        method! visit_de_bruijn_id _ _ = 0
      end
    in
    let method_args =
      PureUtils.bound_generic_args_of_params
        (reset#visit_generic_params () sg.generics)
    in
    {
      types = trait_args.types @ method_args.types;
      const_generics = trait_args.const_generics @ method_args.const_generics;
      trait_refs = (self_ref :: trait_args.trait_refs) @ method_args.trait_refs;
    }

  (** Emit [(<cond> <generics> <args>).holds] for a fn [f]. *)
  let emit_holds span ctx fmt generics args (f : Pure.fun_decl) =
    let generics = cond_generics span ctx generics f in
    let head = fun_head f.def_id generics f.signature.output in
    F.pp_open_hovbox fmt 0;
    F.pp_print_string fmt "(";
    Extract.extract_App span ctx fmt ~inside:false ~inside_do:false head args
      f.signature.output;
    F.pp_print_string fmt ").holds";
    F.pp_close_box fmt ()

  (** Register the pre/post conditions in the (local) context *)
  let add_conditions (ctx : ExtractBase.extraction_ctx) ~pre ~post =
    let reg f_opt (ctx : ExtractBase.extraction_ctx) =
      let some (f : Pure.fun_decl) =
        let trans : TranslateCore.pure_fun_translation =
          { f; loops = []; bodies = [] }
        in
        {
          ctx with
          trans_funs = Pure.FunDeclId.Map.add f.def_id trans ctx.trans_funs;
        }
      in
      Option.fold ~some ~none:ctx f_opt
    in
    ctx |> reg pre |> reg post
end

open Helpers

(** Emit the proof of a spec/theorem as [:= by <tactic>]. *)
let emit_proof fmt (p : HaxSpecs.proof) =
  let tactic =
    match p with
    | Admitted -> "sorry"
  in
  F.pp_print_string fmt (":= by " ^ tactic)

(** Emit the pre/post condition function declarations, if present. *)
let emit_conditions ctx fmt ~pre ~post =
  Option.iter (emit_cond ctx fmt) pre;
  Option.iter (emit_cond ctx fmt) post

(** {1 Names}

    The contract of [<fn>] generates [<fn>.pre], [<fn>.post], [<fn>.spec] and
    [<fn>.spec.proof]. The contract of a method [<m>] of a trait [<Trait>]
    generates [<Trait>.<m>.pre] and [<Trait>.<m>.post]. Every trait [<Trait>]
    generates [<Trait>.Lawful]. *)

(** The registered name of [parent] *)
let registered_fun_name (ctx : ExtractBase.extraction_ctx)
    (parent : Pure.fun_decl) : string =
  ExtractBase.ctx_get_raw (Some parent.item_meta.span)
    (FunId (FromLlbc (FunId (FRegular parent.def_id), parent.loop_id)))
    ctx

(** [<fn>.<suffix>] *)
let cond_name (parent_name : string) (suffix : string) : string =
  ExtractBuiltin.flatten_name [ parent_name; suffix ]

let spec_name (parent_name : string) : string =
  ExtractBuiltin.flatten_name [ parent_name; "spec" ]

let proof_name (parent_name : string) : string =
  ExtractBuiltin.flatten_name [ spec_name parent_name; "proof" ]

let lawful_name (trait_name : string) : string =
  ExtractBuiltin.flatten_name [ trait_name; "Lawful" ]

(** The names of the conditions [pre] and [post] of [parent_name] *)
let cond_names (parent_name : string) ~(pre : Pure.fun_decl option)
    ~(post : Pure.fun_decl option) : (Pure.fun_decl * string) list =
  let cond suffix (f : Pure.fun_decl option) =
    Option.map (fun f -> (f, cond_name parent_name suffix)) f
  in
  List.filter_map Fun.id [ cond "pre" pre; cond "post" post ]

(** The names of the conditions, spec and proof of [parent] *)
let generated_names (parent_name : string)
    ({ pre; post; _ } : HaxSpecs.function_spec) :
    (Pure.fun_decl * string) list * string * string =
  ( cond_names parent_name ~pre ~post,
    spec_name parent_name,
    proof_name parent_name )

(** Lookup the function a spec is about *)
let lookup_parent (ctx : ExtractBase.extraction_ctx) (fn : Pure.FunDeclId.id) :
    Pure.fun_decl option =
  Option.map
    (fun (ft : TranslateCore.pure_fun_translation) -> ft.f)
    (Pure.FunDeclId.Map.find_opt fn ctx.trans_funs)

(** Register the names of conditions, under the ids of their fns *)
let register_conds span (conds : (Pure.fun_decl * string) list)
    (ctx : ExtractBase.extraction_ctx) : ExtractBase.extraction_ctx =
  List.fold_left
    (fun ctx ((f : Pure.fun_decl), name) ->
      ExtractBase.ctx_add span
        (FunId (FromLlbc (FunId (FRegular f.def_id), None)))
        name ctx)
    ctx conds

(** Warn that the contract of an untranslated item is dropped. We use the span
    of the LLBC item [item_meta], if found, and [opt_span] otherwise. *)
let warn_untranslated (ctx : ExtractBase.extraction_ctx) opt_span
    (item_meta : Types.item_meta option) (kind : string) (id : string) =
  let span, name =
    match item_meta with
    | Some m -> (Some m.span, TranslateCore.name_to_string ctx.trans_ctx m.name)
    | None -> (opt_span, id)
  in
  [%warn_opt_span] span
    (Printf.sprintf
       "hax-specs: dropping the contract of %s `%s`: the %s was not translated"
       kind name kind)

(** Register the names of the conditions and of the spec. Must be called after
    registering the crate items. Warns about the specs of untranslated items:
    {!emit_spec} skips them. *)
let register_spec_names (ctx : ExtractBase.extraction_ctx)
    (spec_id : Spec.SpecId.id) (s : HaxSpecs.spec) (opt_span : Meta.span option)
    : ExtractBase.extraction_ctx =
  match s with
  | FunctionSpec fspec -> (
      match lookup_parent ctx fspec.fn with
      | None ->
          warn_untranslated ctx opt_span
            (Option.map
               (fun (f : LlbcAst.fun_decl) -> f.item_meta)
               (Pure.FunDeclId.Map.find_opt fspec.fn
                  ctx.trans_ctx.crate.fun_decls))
            "function"
            (Pure.FunDeclId.to_string fspec.fn);
          ctx
      | Some parent ->
          let span = parent.item_meta.span in
          let conds, spec, _ =
            generated_names (registered_fun_name ctx parent) fspec
          in
          let ctx = register_conds span conds ctx in
          ExtractBase.ctx_add span (SpecId spec_id) spec ctx)
  | TraitSpec { trait_decl; methods } -> (
      match Pure.TraitDeclId.Map.find_opt trait_decl ctx.trans_trait_decls with
      | None ->
          warn_untranslated ctx opt_span
            (Option.map
               (fun (d : LlbcAst.trait_decl) -> d.item_meta)
               (Pure.TraitDeclId.Map.find_opt trait_decl
                  ctx.trans_ctx.crate.trait_decls))
            "trait"
            (Pure.TraitDeclId.to_string trait_decl);
          ctx
      | Some d ->
          let span = d.item_meta.span in
          let get id = ExtractBase.ctx_get_raw (Some span) id ctx in
          let trait_name = get (TraitDeclId trait_decl) in
          let ctx =
            ExtractBase.ctx_add span (SpecId spec_id) (lawful_name trait_name)
              ctx
          in
          List.fold_left
            (fun ctx ({ method_id; pre; post } : HaxSpecs.method_spec) ->
              let method_name = get (TraitMethodId (trait_decl, method_id)) in
              register_conds span
                (cond_names
                   (ExtractBuiltin.flatten_name [ trait_name; method_name ])
                   ~pre ~post)
                ctx)
            ctx methods)

(** Same as {!register_spec_names}, for a proof obligation *)
let register_obligation_names (ctx : ExtractBase.extraction_ctx)
    (proof_id : Spec.ProofId.id) (o : HaxSpecs.obligation) :
    ExtractBase.extraction_ctx =
  match o with
  | FunctionContract { spec = fspec; _ } -> (
      match lookup_parent ctx fspec.fn with
      | None -> ctx
      | Some parent ->
          let _, _, proof =
            generated_names (registered_fun_name ctx parent) fspec
          in
          ExtractBase.ctx_add parent.item_meta.span (ProofObligationId proof_id)
            proof ctx)
  | ImplLawful _ -> (* Not produced yet *) ctx

(** Emits the spec statement — the body of [def foo.spec … : Prop :=] (the
    [theorem foo.spec.proof … := by sorry] wrapper is the obligation, emitted
    separately):
    {[
      (foo.pre args).holds →
      ⦃ ⌜ True ⌝ ⦄
      foo args
      ⦃ ⇓ res => ⌜ (foo.post args res).holds ⌝ ⦄
    ]}
    [head] is the function applied ([foo]), and [generics] the generics from
    which those of the conditions are computed. *)
let emit_statement ctx fmt span (head : Pure.texpr) generics output_ty
    arg_texprs res_id ~(pre : Pure.fun_decl option)
    ~(post : Pure.fun_decl option) =
  let open ExtractBase in
  (* Register the postcondition's result variable *)
  let ctx, res_name = ctx_add_var span "res" res_id ctx in
  let res_texpr : Pure.texpr = { e = FVar res_id; ty = output_ty } in
  let emit_holds = emit_holds span ctx fmt generics in
  let emit_pure k = Extract.emit_delim ~add_spaces:false fmt "⌜ " k " ⌝" in

  (* Optional pre-hypothesis: [(<fn>.pre <args>).holds →]. *)
  (match pre with
  | None -> ()
  | Some pre_fn ->
      line fmt (fun () ->
          emit_holds arg_texprs pre_fn;
          F.pp_print_space fmt ();
          F.pp_print_string fmt "→"));

  (* The (trivial) triple precondition. *)
  line fmt (fun () ->
      emit_wp fmt (fun () -> emit_pure (fun () -> F.pp_print_string fmt "True")));

  (* The real function application [<fn> <args>], via the standard printer. *)
  line fmt (fun () ->
      Extract.extract_App span ctx fmt ~inside:false ~inside_do:false head
        arg_texprs output_ty);

  (* The triple postcondition: [(<fn>.post <args> res).holds], or [True] when
     the function has no postcondition. *)
  line fmt (fun () ->
      emit_wp fmt (fun () ->
          emit_words fmt [ "⇓"; res_name; "=>" ];
          F.pp_print_break fmt 1 ctx.indent_incr;
          emit_pure (fun () ->
              match post with
              | None -> F.pp_print_string fmt "True"
              | Some post_fn -> emit_holds (arg_texprs @ [ res_texpr ]) post_fn)))

(** {1 Lawful structures} *)

(** The instance an [X.Lawful] structure is about, for the trait [d]: a fresh
    clause [<X>Inst : <X> <params>] registered in [ctx] (where the parameters of
    [d] must be registered), its name and a reference to it. It is named like
    the clause [Self_: <X>] of the conditions, as
    {!ExtractBase.ctx_compute_trait_clause_basename} does for Lean. *)
let lawful_instance span (ctx : ExtractBase.extraction_ctx)
    (d : Pure.trait_decl) :
    ExtractBase.extraction_ctx * Pure.trait_param * string * Pure.trait_ref =
  let clause : Pure.trait_param =
    {
      (* The clause ids are positions *)
      clause_id =
        Pure.TraitClauseId.of_int (List.length d.generics.trait_clauses);
      trait_id = d.def_id;
      generics = PureUtils.generic_args_of_params d.generics;
    }
  in
  let basename =
    String.concat ""
      (TranslateCore.trait_name_with_generics_to_simple_name ctx.trans_ctx
         ~prefix:(Some (fst (Collections.List.pop_last d.item_meta.name)))
         d.item_meta.name d.llbc_generics
         (Charon.TypesUtils.generic_args_of_params (Some span) d.llbc_generics))
    ^ "Inst"
  in
  let ctx, name =
    ExtractBase.ctx_add_local_trait_clause span Item basename clause.clause_id
      ctx
  in
  let tr =
    match
      (PureUtils.generic_args_of_params
         { PureUtils.empty_generic_params with trait_clauses = [ clause ] })
        .trait_refs
    with
    | [ tr ] -> tr
    | _ -> [%internal_error] span
  in
  (ctx, clause, name, tr)

(** Emit [<X>.Lawful <args> <tr>]: the Lawful structure of the trait [tr] is an
    instance of, applied to it *)
let emit_lawful_type span (ctx : ExtractBase.extraction_ctx) fmt
    (tr : Pure.trait_ref) =
  let decl_ref = tr.trait_decl_ref in
  let name =
    ExtractBase.ctx_get_raw (Some span) (TraitDeclId decl_ref.trait_decl_id) ctx
  in
  F.pp_print_string fmt (ExtractBase.escape_name (lawful_name name));
  (* The arguments, as for the trait (see {!ExtractTypes.extract_trait_decl_ref}) *)
  let explicit =
    Option.map
      (fun (d : Pure.trait_decl) -> d.explicit_info)
      (Pure.TraitDeclId.Map.find_opt decl_ref.trait_decl_id
         ctx.trans_trait_decls)
  in
  ExtractTypes.extract_generic_args span ctx fmt Pure.TypeDeclId.Set.empty
    ~explicit
    { decl_ref.decl_generics with trait_refs = [] };
  F.pp_print_space fmt ();
  ExtractTypes.extract_trait_ref span ctx fmt Pure.TypeDeclId.Set.empty
    ~inside:true tr

(** Emit the binders of the trait clauses [clauses] (bound at [origin]), each
    followed by its Lawful binder:
    [(<C> : <X> <args>) (<C>Lawful : <X>.Lawful <args> <C>)] *)
let emit_lawful_clause_binders span (ctx : ExtractBase.extraction_ctx) fmt
    (origin : ExtractBase.generic_origin) (clauses : Pure.trait_param list) =
  let args =
    (match origin with
    | Item -> PureUtils.generic_args_of_params
    | Method -> PureUtils.bound_generic_args_of_params)
      { PureUtils.empty_generic_params with trait_clauses = clauses }
  in
  List.iter2
    (fun (c : Pure.trait_param) tr ->
      let name =
        ExtractBase.ctx_get_local_trait_clause span origin c.clause_id ctx
      in
      emit_binder fmt name (fun () ->
          ExtractTypes.extract_trait_clause_type span ctx fmt
            Pure.TypeDeclId.Set.empty c);
      emit_binder fmt (name ^ "Lawful") (fun () ->
          emit_lawful_type span ctx fmt tr))
    clauses args.trait_refs

(** Emit the [Lawful] structure of the trait [d], whose annotated methods are
    [methods]: one field per parent clause of the trait, then one per annotated
    method. The arguments of the methods are named as in their conditions. *)
let emit_lawful_structure (ctx : ExtractBase.extraction_ctx) fmt
    (d : Pure.trait_decl) (methods : HaxSpecs.method_spec list) =
  let open ExtractBase in
  let span = d.item_meta.span in
  let no_params_tys = Pure.TypeDeclId.Set.empty in
  let ctx, type_params, cg_params, trait_clauses =
    ctx_add_generic_params span d.item_meta.name Item d.llbc_generics d.generics
      ctx
  in
  let ctx, self_clause, self_name, self_ref = lawful_instance span ctx d in
  (* Link the structure to the trait declaration *)
  ExtractTypes.extract_comment_with_span ctx fmt
    [
      "Lawful structure of trait: [" ^ name_to_string ctx d.item_meta.name ^ "]";
    ]
    None span;
  F.pp_print_break fmt 0 0;
  F.pp_open_vbox fmt ctx.indent_incr;
  (* [structure <X>.Lawful <params> (<X>Inst : <X> <params>) : Prop where] *)
  F.pp_open_hovbox fmt ctx.indent_incr;
  F.pp_print_string fmt "structure";
  F.pp_print_space fmt ();
  F.pp_print_string fmt
    (escape_name
       (lawful_name (ctx_get_raw (Some span) (TraitDeclId d.def_id) ctx)));
  ExtractTypes.extract_generic_params span ctx fmt no_params_tys Item
    {
      d.generics with
      trait_clauses = d.generics.trait_clauses @ [ self_clause ];
    }
    (Some d.explicit_info) type_params cg_params
    (trait_clauses @ [ self_name ]);
  F.pp_print_space fmt ();
  F.pp_print_string fmt ":";
  F.pp_print_space fmt ();
  F.pp_print_string fmt "Prop";
  if d.parent_clauses <> [] || methods <> [] then (
    F.pp_print_space fmt ();
    F.pp_print_string fmt "where");
  F.pp_close_box fmt ();
  (* The parents: [<P>Lawful : <P>.Lawful <args> <X>Inst.<P>] *)
  List.iter
    (fun (c : Pure.trait_param) ->
      let name =
        ctx_get_raw (Some span)
          (TraitParentClauseId (d.def_id, c.clause_id))
          ctx
      in
      Extract.extract_trait_decl_item ctx fmt
        (escape_name (name ^ "Lawful"))
        (fun () ->
          F.pp_print_space fmt ();
          emit_lawful_type span ctx fmt (parent_ref d self_ref c)))
    d.parent_clauses;
  (* The annotated methods: [<m>_spec <binders> : <statement>] *)
  List.iter
    (fun ({ method_id; pre; post } : HaxSpecs.method_spec) ->
      let m =
        match
          List.find_opt
            (fun (m : Pure.trait_method) -> m.method_id = method_id)
            d.methods
        with
        | Some m -> m
        | None -> [%internal_error] span
      in
      let sg = m.signature in
      let ctx, type_params, cg_params, clause_names =
        ctx_add_generic_params span m.item_meta.name Method sg.llbc_generics
          sg.generics ctx
      in
      (* The names of the Lawful binders of the clauses *)
      let ctx =
        ctx_reserve_names (List.map (fun n -> n ^ "Lawful") clause_names) ctx
      in
      let ctx = add_conditions ctx ~pre ~post in
      let _, fresh_fvar_id = Pure.FVarId.fresh_stateful_generator () in
      let ctx, args = method_args span ctx fresh_fvar_id sg pre in
      F.pp_print_space fmt ();
      F.pp_open_vbox fmt ctx.indent_incr;
      F.pp_open_hovbox fmt ctx.indent_incr;
      F.pp_print_string fmt
        (escape_name
           (ctx_get_raw (Some span) (TraitMethodId (d.def_id, method_id)) ctx
           ^ "_spec"));
      ExtractTypes.extract_generic_params span ctx fmt no_params_tys Method
        { sg.generics with trait_clauses = [] }
        (Some sg.explicit_info) type_params cg_params [];
      emit_lawful_clause_binders span ctx fmt Method sg.generics.trait_clauses;
      List.iter
        (fun (a : Pure.texpr) ->
          emit_binder fmt
            (ctx_get_var span (PureUtils.as_fvar span a) ctx)
            (fun () ->
              ExtractTypes.extract_ty span ctx fmt no_params_tys ~inside:false
                a.ty))
        args;
      F.pp_print_space fmt ();
      F.pp_print_string fmt ":";
      F.pp_close_box fmt ();
      let head : Pure.texpr =
        {
          e =
            Qualif
              {
                id =
                  FunOrOp
                    (Fun (FromLlbc (TraitMethod (self_ref, method_id), None)));
                generics = PureUtils.bound_generic_args_of_params sg.generics;
              };
          ty = sg.output;
        }
      in
      let output =
        if sg.fwd_info.effect_info.can_fail then
          PureUtils.unwrap_result_ty span sg.output
        else sg.output
      in
      emit_statement ctx fmt span head
        (method_generics d self_ref sg)
        output args (fresh_fvar_id ()) ~pre ~post;
      F.pp_close_box fmt ())
    methods;
  F.pp_close_box fmt ()

(** Emit one [Spec.spec] entry *)
let emit_spec ctx fmt (s : HaxSpecs.spec) =
  let open ExtractBase in
  match s with
  | FunctionSpec { fn; pre; post } -> (
      match Pure.FunDeclId.Map.find_opt fn ctx.trans_funs with
      | None -> (* Reported by [register_spec_names] *) ()
      | Some ft ->
          let ctx = add_conditions ctx ~pre ~post in
          let parent = ft.f in
          let span = parent.item_meta.span in
          let sg = parent.signature in
          let generics = PureUtils.generic_args_of_params sg.generics in

          (* Open the parent's body binders *)
          let _, fresh_fvar_id = Pure.FVarId.fresh_stateful_generator () in
          let parent =
            {
              parent with
              body =
                Option.map
                  (fun b ->
                    snd (PureUtils.open_all_fun_body fresh_fvar_id span b))
                  parent.body;
            }
          in
          let arg_texprs =
            match parent.body with
            | None -> []
            | Some { inputs; _ } -> input_args span inputs
          in
          (* Fresh result-var id, from the body generator so it can't clash. *)
          let res_id = fresh_fvar_id () in

          (* The leading break of the conditions separates the entry *)
          emit_conditions ctx fmt ~pre ~post;

          (* Spec definition header: [def <fn>.spec <binders> : Prop :=] *)
          F.pp_print_break fmt 0 0;
          F.pp_open_vbox fmt 0;
          F.pp_open_vbox fmt ctx.indent_incr;
          F.pp_open_hovbox fmt ctx.indent_incr;
          (match fun_decl_kind_to_qualif SingleNonRec with
          | Some qualif ->
              F.pp_print_string fmt qualif;
              F.pp_print_space fmt ()
          | None -> ());
          F.pp_print_string fmt
            (escape_name (spec_name (registered_fun_name ctx parent)));
          (* Generic + value binders via the standard param extractor. *)
          let space = ref false in
          let _, ctx, _ = Extract.extract_fun_parameters space ctx fmt parent in
          ExtractTypes.insert_req_space fmt space;
          F.pp_print_string fmt ": Prop :=";
          F.pp_close_box fmt ();

          (* Statement shape (the def body). *)
          emit_statement ctx fmt span
            (fun_head fn generics sg.output)
            generics sg.output arg_texprs res_id ~pre ~post;
          F.pp_close_box fmt ();
          (* inner vbox *)
          F.pp_close_box fmt ();
          (* outer vbox *)
          F.pp_print_cut fmt ())
  | TraitSpec { trait_decl; _ }
    when not (Pure.TraitDeclId.Map.mem trait_decl ctx.trans_trait_decls) ->
      (* Reported by [register_spec_names] *) ()
  | TraitSpec { trait_decl; methods } ->
      (* The conditions of the annotated methods *)
      List.iter
        (fun ({ pre; post; _ } : HaxSpecs.method_spec) ->
          emit_conditions ctx fmt ~pre ~post)
        methods;
      (* Blank line before the structure. *)
      F.pp_print_break fmt 0 0;
      emit_lawful_structure ctx fmt
        (Pure.TraitDeclId.Map.find trait_decl ctx.trans_trait_decls)
        methods;
      (* New line after the structure. *)
      F.pp_print_break fmt 0 0

(** Emit one [HaxSpecs.obligation] entry as the proof obligation that discharges
    a spec's statement of correctness:
    {[
      theorem foo.spec.proof args : foo.spec args := by sorry
    ]}
    No attribute is emitted: registering the obligation with [mvcgen] (via
    [@[spec]]) is left to the user, who decides which specs to feed it. *)
let emit_obligation ctx fmt (o : HaxSpecs.obligation) =
  let open ExtractBase in
  match o with
  | FunctionContract { spec = { fn; _ }; proof } -> (
      match Pure.FunDeclId.Map.find_opt fn ctx.trans_funs with
      | None -> (* Reported by [register_spec_names] *) ()
      | Some ft ->
          let parent = ft.f in
          let span = parent.item_meta.span in
          let sg = parent.signature in
          let explicit = sg.explicit_info in
          let generics = PureUtils.generic_args_of_params sg.generics in
          let parent_name = registered_fun_name ctx parent in

          (* Open the parent's body binders *)
          let _, fresh_fvar_id = Pure.FVarId.fresh_stateful_generator () in
          let parent =
            {
              parent with
              body =
                Option.map
                  (fun b ->
                    snd (PureUtils.open_all_fun_body fresh_fvar_id span b))
                  parent.body;
            }
          in
          let arg_texprs =
            match parent.body with
            | None -> []
            | Some { inputs; _ } -> input_args span inputs
          in

          (* Blank line before the entry. *)
          F.pp_print_break fmt 0 0;

          (* Box layout (brackets = boxes):
             [ [theorem name] binders : [statement] ]  [:= by sorry]
             The outer [hvbox] keeps the whole theorem on one line if it fits;
             otherwise [:= by sorry] breaks onto its own line first, and only if
             the statement box itself still overflows do the binders/type wrap. *)
          F.pp_open_hvbox fmt ctx.indent_incr;
          (* The theorem statement: [theorem name binders : <type>]. *)
          F.pp_open_hovbox fmt ctx.indent_incr;
          F.pp_print_string fmt "theorem";
          F.pp_print_space fmt ();
          F.pp_print_string fmt (escape_name (proof_name parent_name));
          (* Generic + value binders via the standard param extractor. *)
          let space = ref false in
          let _, ctx, _ = Extract.extract_fun_parameters space ctx fmt parent in
          ExtractTypes.insert_req_space fmt space;
          F.pp_print_string fmt ":";
          F.pp_print_space fmt ();
          (* The statement of correctness, in its own box:
             [<fn>.spec <generics> <args>]. *)
          F.pp_open_hovbox fmt 0;
          emit_app span ctx fmt explicit generics arg_texprs
            (escape_name (spec_name parent_name));
          F.pp_close_box fmt ();
          F.pp_close_box fmt ();
          (* statement hovbox *)
          F.pp_print_space fmt ();
          emit_proof fmt proof;
          F.pp_close_box fmt ();
          (* outer hvbox *)
          F.pp_print_cut fmt ())
  | ImplLawful _ -> (* Not produced yet *) ()
