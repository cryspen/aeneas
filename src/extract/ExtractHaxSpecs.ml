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
    Extract.emit_delim fmt "⦃" k "⦄"

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

  (** The generics to pass to a pre/post condition [cond], from the [generics]
      of the function it describes. The types and const generics match, but the
      trait clauses may not: for [trait B: A], the conditions of a method of [B]
      have clauses [Self_: A] and [Self_: B], while the method only has
      [Self: B]. We look up each clause of [cond] among the trait refs of
      [generics] and their parent clauses. *)
  let cond_generics span (ctx : ExtractBase.extraction_ctx)
      (generics : Pure.generic_args) (cond : Pure.fun_decl) : Pure.generic_args
      =
    let rec with_parents (tr : Pure.trait_ref) : Pure.trait_ref list =
      let decl_ref = tr.trait_decl_ref in
      match
        Pure.TraitDeclId.Map.find_opt decl_ref.trait_decl_id
          ctx.trans_trait_decls
      with
      | None -> [ tr ]
      | Some d ->
          let subst =
            PureUtils.make_subst_from_generics_for_trait d.generics tr.trait_id
              decl_ref.decl_generics
          in
          let parent (c : Pure.trait_param) : Pure.trait_ref =
            {
              trait_id = ParentClause (tr.trait_id, d.def_id, c.clause_id);
              trait_decl_ref =
                {
                  trait_decl_id = c.trait_id;
                  decl_generics =
                    PureUtils.generic_args_substitute subst c.generics;
                };
            }
          in
          tr
          :: List.concat_map (fun c -> with_parents (parent c)) d.parent_clauses
    in
    let available = List.concat_map with_parents generics.trait_refs in
    let find (c : Pure.trait_param) : Pure.trait_ref =
      let decl_ref : Pure.trait_decl_ref =
        { trait_decl_id = c.trait_id; decl_generics = c.generics }
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
    [<fn>.spec.proof]. *)

(** The registered name of [parent] *)
let registered_fun_name (ctx : ExtractBase.extraction_ctx)
    (parent : Pure.fun_decl) : string =
  ExtractBase.ctx_get_raw (Some parent.item_meta.span)
    (FunId (FromLlbc (FunId (FRegular parent.def_id), parent.loop_id)))
    ctx

(** [<fn>.<suffix>]. The conditions of a default method
    [<Trait>.<method>.default] are [<Trait>.<method>.pre] / [.post]: their
    naming is left open for now. *)
let cond_name (ctx : ExtractBase.extraction_ctx) (parent : Pure.fun_decl)
    (parent_name : string) (suffix : string) : string =
  let base =
    if ExtractBase.fun_source_is_trait_default ctx parent.src then
      let default_suffix = "." ^ ExtractBase.trait_default_method_suffix in
      match Filename.chop_suffix_opt ~suffix:default_suffix parent_name with
      | Some base -> base
      | None -> [%internal_error] parent.item_meta.span
    else parent_name
  in
  base ^ "." ^ suffix

let spec_name (parent_name : string) : string = parent_name ^ ".spec"

let proof_name (parent_name : string) : string =
  spec_name parent_name ^ ".proof"

(** The names of the conditions, spec and proof of [parent] *)
let generated_names ctx (parent : Pure.fun_decl) (parent_name : string)
    ({ pre; post; _ } : HaxSpecs.function_spec) :
    (Pure.fun_decl * string) list * string * string =
  let cond suffix (f : Pure.fun_decl option) =
    Option.map (fun f -> (f, cond_name ctx parent parent_name suffix)) f
  in
  ( List.filter_map Fun.id [ cond "pre" pre; cond "post" post ],
    spec_name parent_name,
    proof_name parent_name )

(** Lookup the function a spec is about *)
let lookup_parent (ctx : ExtractBase.extraction_ctx) (fn : Pure.FunDeclId.id) :
    Pure.fun_decl option =
  Option.map
    (fun (ft : TranslateCore.pure_fun_translation) -> ft.f)
    (Pure.FunDeclId.Map.find_opt fn ctx.trans_funs)

(** Register the names of the conditions and of the spec. Must be called after
    registering the crate items. *)
let register_spec_names (ctx : ExtractBase.extraction_ctx)
    (spec_id : Spec.SpecId.id) (s : HaxSpecs.spec) : ExtractBase.extraction_ctx
    =
  match s with
  | FunctionSpec fspec -> (
      match lookup_parent ctx fspec.fn with
      | None -> ctx
      | Some parent ->
          let span = parent.item_meta.span in
          let conds, spec, _ =
            generated_names ctx parent (registered_fun_name ctx parent) fspec
          in
          let ctx =
            List.fold_left
              (fun ctx ((f : Pure.fun_decl), name) ->
                ExtractBase.ctx_add span
                  (FunId (FromLlbc (FunId (FRegular f.def_id), None)))
                  name ctx)
              ctx conds
          in
          ExtractBase.ctx_add span (SpecId spec_id) spec ctx)

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
            generated_names ctx parent (registered_fun_name ctx parent) fspec
          in
          ExtractBase.ctx_add parent.item_meta.span (ProofObligationId proof_id)
            proof ctx)

(** Emits the spec statement — the body of [def foo.spec … : Prop :=] (the
    [theorem foo.spec.proof … := by sorry] wrapper is the obligation, emitted
    separately):
    {[
      (foo.pre args).holds →
      ⦃ ⌜ True ⌝ ⦄
      foo args
      ⦃ ⇓ res => ⌜ (foo.post args res).holds ⌝ ⦄
    ]} *)
let emit_statement ctx fmt span (fn : Pure.FunDeclId.id) generics output_ty
    arg_texprs res_id ~(pre : Pure.fun_decl option)
    ~(post : Pure.fun_decl option) =
  let open ExtractBase in
  (* Register the postcondition's result variable *)
  let ctx, res_name = ctx_add_var span "res" res_id ctx in
  let res_texpr : Pure.texpr = { e = FVar res_id; ty = output_ty } in
  let emit_holds = emit_holds span ctx fmt generics in
  let emit_pure k = Extract.emit_delim fmt "⌜" k "⌝" in

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
      let head = fun_head fn generics output_ty in
      Extract.extract_App span ctx fmt ~inside:false ~inside_do:false head
        arg_texprs output_ty);

  (* The triple postcondition: [(<fn>.post <args> res).holds], or [True] when
     the function has no postcondition. *)
  line fmt (fun () ->
      emit_wp fmt (fun () ->
          emit_words fmt [ "⇓"; res_name; "=>" ];
          F.pp_print_space fmt ();
          emit_pure (fun () ->
              match post with
              | None -> F.pp_print_string fmt "True"
              | Some post_fn -> emit_holds (arg_texprs @ [ res_texpr ]) post_fn)))

(** Emit one [Spec.spec] entry *)
let emit_spec ctx fmt (s : HaxSpecs.spec) opt_span =
  let open ExtractBase in
  match s with
  | FunctionSpec { fn; pre; post } -> (
      match Pure.FunDeclId.Map.find_opt fn ctx.trans_funs with
      | None ->
          [%warn_opt_span] opt_span
            ("Trying to print a spec for an unknown function '"
            ^ Pure.FunDeclId.to_string fn
            ^ "'")
      | Some ft ->
          (* Register the pre/post conditions in the (local) context *)
          let reg f_opt ctx =
            let some (f : Pure.fun_decl) =
              let trans : TranslateCore.pure_fun_translation =
                { f; loops = []; bodies = [] }
              in
              {
                ctx with
                trans_funs =
                  Pure.FunDeclId.Map.add f.def_id trans ctx.trans_funs;
              }
            in
            Option.fold ~some ~none:ctx f_opt
          in
          let ctx = ctx |> reg pre |> reg post in
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

          (* Blank line before the entry. *)
          F.pp_print_break fmt 0 0;

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
          emit_statement ctx fmt span fn generics sg.output arg_texprs res_id
            ~pre ~post;
          F.pp_close_box fmt ();
          (* inner vbox *)
          F.pp_close_box fmt ();
          (* outer vbox *)
          F.pp_print_cut fmt ())

(** Emit one [HaxSpecs.obligation] entry as the proof obligation that discharges
    a spec's statement of correctness:
    {[
      theorem foo.spec.proof args : foo.spec args := by sorry
    ]}
    No attribute is emitted: registering the obligation with [mvcgen] (via
    [@[spec]]) is left to the user, who decides which specs to feed it. *)
let emit_obligation ctx fmt (o : HaxSpecs.obligation) opt_span =
  let open ExtractBase in
  match o with
  | FunctionContract { spec = { fn; _ }; proof } -> (
      match Pure.FunDeclId.Map.find_opt fn ctx.trans_funs with
      | None ->
          [%warn_opt_span] opt_span
            ("Trying to print a proof obligation for an unknown function '"
            ^ Pure.FunDeclId.to_string fn
            ^ "'")
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
