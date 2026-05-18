open Types
open Values
open Expressions
open Contexts

(** Translate the rvalue half of an [Event.Assign]. Mirrors the
    inline cert-side dispatch the original
    [InterpStatements.eval_statement_raw Assign] arm did. Returns
    [None] when the rvalue shape doesn't map to a cert payload (e.g.
    operands that don't lift, raw pointers, …). -*)
let assign_to_cert (ctx : eval_ctx) (dst : place) (rvalue : rvalue)
    : CertEvent.event option =
  let mk_evassign rhs : CertEvent.event option =
    match CertEvent.cert_place_of_place dst with
    | Some cp -> Some (CertEvent.EvAssign { dst = cp; rhs })
    | None -> None
  in
  match rvalue with
  | Use operand ->
      (match CertEvent.cert_sym_expr_of_operand operand with
       | Some rhs -> mk_evassign rhs
       | None -> None)
  | Aggregate
      ( AggregatedAdt
          ( { id = TAdtId def_id; _ }, Some variant_id, None ),
        operands ) ->
      (* M9.5d / M9.5f: enum-variant ADT construction. *)
      let variant_name =
        match TypeDeclId.Map.find_opt def_id ctx.crate.type_decls with
        | Some td ->
            (match td.kind with
             | Enum variants ->
                 (VariantId.nth variants variant_id).variant_name
             | _ -> "Variant")
        | None -> "Variant"
      in
      let fields_opt =
        List.fold_right
          (fun op acc ->
            match acc with
            | None -> None
            | Some xs ->
                (match CertEvent.cert_sym_expr_of_operand op with
                 | Some e -> Some (e :: xs)
                 | None -> None))
          operands (Some [])
      in
      (match fields_opt with
       | Some fields ->
           mk_evassign
             (CertEvent.SymVariant {
               adt_id = TypeDeclId.to_int def_id;
               variant_id = VariantId.to_int variant_id;
               variant_name; fields;
             })
       | None -> None)
  | Aggregate
      ( AggregatedAdt
          ( { id = TTuple; _ }, None, None ),
        operands ) ->
      (* M9.5p: tuple aggregate `(x, y, ...)`. *)
      let fields_opt =
        List.fold_right
          (fun op acc ->
            match acc with
            | None -> None
            | Some xs ->
                (match CertEvent.cert_sym_expr_of_operand op with
                 | Some e -> Some (e :: xs)
                 | None -> None))
          operands (Some [])
      in
      (match fields_opt with
       | Some fields -> mk_evassign (CertEvent.SymTuple fields)
       | None -> None)
  | Aggregate
      ( AggregatedAdt
          ( { id = TAdtId def_id; _ }, None, None ),
        operands ) ->
      (* M9.5p: named-field struct aggregate `Pair { x, y }`. *)
      let field_names : string list =
        match TypeDeclId.Map.find_opt def_id ctx.crate.type_decls with
        | Some td -> (
            match td.kind with
            | Struct fields ->
                List.mapi
                  (fun i (f : field) ->
                    match f.field_name with
                    | Some n -> n
                    | None -> "field" ^ string_of_int i)
                  fields
            | _ ->
                List.mapi (fun i _ -> "field" ^ string_of_int i) operands)
        | None ->
            List.mapi (fun i _ -> "field" ^ string_of_int i) operands
      in
      let fields_opt =
        let rec pair_up names ops =
          match names, ops with
          | [], [] -> Some []
          | n :: ns, op :: rest ->
              (match CertEvent.cert_sym_expr_of_operand op with
               | None -> None
               | Some e ->
                   (match pair_up ns rest with
                    | None -> None
                    | Some xs -> Some ((n, e) :: xs)))
          | _, _ -> None
        in
        pair_up field_names operands
      in
      (match fields_opt with
       | Some fields ->
           mk_evassign
             (CertEvent.SymRecord {
               adt_id = TypeDeclId.to_int def_id; fields;
             })
       | None -> None)
  | UnaryOp (Cast (CastScalar (_src_ty, dst_ty)), operand) ->
      (* Session 6 Item 1: `as`-cast at the rvalue level. *)
      let target_ty : string = match dst_ty with
        | TInt Isize -> "isize"
        | TInt I8 -> "i8"
        | TInt I16 -> "i16"
        | TInt I32 -> "i32"
        | TInt I64 -> "i64"
        | TInt I128 -> "i128"
        | TUInt Usize -> "usize"
        | TUInt U8 -> "u8"
        | TUInt U16 -> "u16"
        | TUInt U32 -> "u32"
        | TUInt U64 -> "u64"
        | TUInt U128 -> "u128"
        | TBool -> "bool"
        | TChar -> "char"
        | TFloat _ -> "float"
      in
      (match CertEvent.cert_sym_expr_of_operand operand with
       | Some inner ->
           mk_evassign (CertEvent.SymCast { target_ty; inner })
       | None -> None)
  | RvRef (rp, (BMut | BTwoPhaseMut | BUniqueImmutable), _) ->
      (* M12.2a: reborrow assignment carries the dst place so the
         walker's `vm` learns vm[N] := lookup(rp). *)
      (match CertEvent.cert_place_of_place rp with
       | Some crp -> mk_evassign (CertEvent.SymCopy crp)
       | None -> None)
  | _ -> None

(** Translate an interpreter-native [Event.t] into the corresponding
    [CertEvent.event]. Returns [None] when:
    * the event has no cert representation (typically because operands
      reference globals or other shapes the cert can't lift), or
    * the event's migration has not landed yet (commits 3-9 grow this
      function one variant at a time).

    Commits 3-9 of the observer-refactor migration sequence each
    extend this with new [Event.X -> CertEvent.EvX] cases. -*)
let event_to_cert (ctx : eval_ctx) (ev : Event.t) : CertEvent.event option =
  match ev with
  | Event.Copy { src; dst } ->
      (* The src/dst arrive as a single [place] from the interpreter,
         already paired. Translation fails when the place references a
         global; the inline emit site used to elide it then, so we do
         the same. *)
      (match CertEvent.cert_place_of_place src,
             CertEvent.cert_place_of_place dst with
       | Some cp_src, Some cp_dst ->
           Some (CertEvent.EvCopy { src = cp_src; dst = cp_dst })
       | _ -> None)
  | Event.Move { src; dst } ->
      (match CertEvent.cert_place_of_place src,
             CertEvent.cert_place_of_place dst with
       | Some cp_src, Some cp_dst ->
           Some (CertEvent.EvMove { src = cp_src; dst = cp_dst })
       | _ -> None)
  | Event.Reborrow { child; parent; place; parent_live; parent_abs } ->
      (match CertEvent.cert_place_of_place place with
       | Some cp ->
           Some (CertEvent.EvReborrow {
             child; parent; place = cp; parent_live; parent_abs;
           })
       | None -> None)
  | Event.EndBorrow { loan; borrowed_value } ->
      (* M9.6 (Option C, plan §4.1.6): dedupe against
         [cert_ended_loans] so the M9.5x redundant post-join
         EvEndBorrow on the same loan id collapses to a single
         emit. The OCaml join machinery linearises each branch's
         cleanup separately and may re-walk the same loan during
         reconciliation. The on_event suppression guard above ensures
         loop-fixpoint speculative iterations don't poison the set. *)
      if BorrowId.Set.mem loan !(ctx.cert_ended_loans) then None
      else begin
        ctx.cert_ended_loans :=
          BorrowId.Set.add loan !(ctx.cert_ended_loans);
        let given_back : CertEvent.cert_sym_expr =
          match borrowed_value with
          | Some bv -> (
              match bv.value with
              | VSymbolic sv -> CertEvent.SymVal sv.sv_id
              | VLiteral lit -> CertEvent.SymLit lit
              | _ -> CertEvent.SymMutBorrowTok loan)
          | None -> CertEvent.SymMutBorrowTok loan
        in
        (* M10.x.0 (cert v6 #11): record which env local holds the
           [VMutLoan loan] token. Observer fires *pre*-give-back so
           the token is still present. -*)
        let ri_holder_local : LocalId.id option =
          let found = ref None in
          List.iter
            (fun (e : env_elem) ->
              if Option.is_none !found then
                match e with
                | EBinding (BVar bv, v) ->
                  (match v.value with
                   | VLoan (VMutLoan b) when b = loan ->
                     found := Some bv.index
                   | _ -> ())
                | _ -> ())
            ctx.env;
          !found
        in
        Some (CertEvent.EvEndBorrow {
          loan;
          restore = { ri_given_back = given_back; ri_holder_local };
        })
      end
  | Event.EndAbs { abs_id; abs_value; pre_end_env } ->
      let cert_final_values, cert_released_loans =
        match abs_value with
        | None -> ([], [])
        | Some abs ->
            let fvs = ref [] in
            let rls = ref [] in
            let visitor =
              object
                inherit [_] iter_abs as super

                method! visit_AEndedMutBorrow env meta child =
                  fvs := CertEvent.SymVal meta.given_back.sv_id :: !fvs;
                  (* M9.5s: abstraction-internal borrow id whose
                     lifetime ends implicitly here. -*)
                  rls := meta.bid :: !rls;
                  super#visit_AEndedMutBorrow env meta child

                method! visit_AEndedProjBorrows env aproj =
                  fvs :=
                    CertEvent.SymVal aproj.mvalues.given_back.sv_id :: !fvs;
                  super#visit_AEndedProjBorrows env aproj
              end
            in
            visitor#visit_abs () abs;
            (List.rev !fvs, List.rev !rls)
      in
      (* M9.6 (Option C): collect locals holding [VMutLoan bid] for
         each [bid] in [cert_released_loans]. Scan [pre_end_env]
         (the ctx0 snapshot from the top of [end_abs_aux]) because
         [end_abs_borrows] has already substituted those tokens
         away by emit time. -*)
      let cert_token_clear_locals : LocalId.id list =
        if cert_released_loans = [] then []
        else begin
          let released = BorrowId.Set.of_list cert_released_loans in
          let acc = ref [] in
          List.iter
            (fun (e : env_elem) ->
              match e with
              | EBinding (BVar bv, v) ->
                let visitor = object
                  inherit [_] iter_tvalue as super
                  method! visit_VMutLoan env bid =
                    if BorrowId.Set.mem bid released then
                      if not (List.mem bv.index !acc) then
                        acc := bv.index :: !acc;
                    super#visit_VMutLoan env bid
                end in
                visitor#visit_tvalue () v
              | _ -> ())
            pre_end_env;
          List.rev !acc
        end
      in
      Some (CertEvent.EvEndAbs {
        abs = abs_id;
        final_values = cert_final_values;
        released_loans = cert_released_loans;
        token_clear_locals = cert_token_clear_locals;
      })
  | Event.Assert { cond_value; expected } ->
      let cond : CertEvent.cert_sym_expr =
        match cond_value.value with
        | VSymbolic sv -> CertEvent.SymVal sv.sv_id
        | VLiteral lit -> CertEvent.SymLit lit
        | _ -> CertEvent.SymVal (SymbolicValueId.of_int 0)
      in
      Some (CertEvent.EvAssert { cond; expected })
  | Event.Panic -> Some CertEvent.EvPanic
  | Event.Return -> Some CertEvent.EvReturn
  | Event.MatchArm { scrutinee; adt_id; variant_id; variant_name } ->
      let scrutinee_se : CertEvent.cert_sym_expr =
        match scrutinee.value with
        | VSymbolic sv -> CertEvent.SymVal sv.sv_id
        | _ -> CertEvent.SymVal (SymbolicValueId.of_int 0)
      in
      Some (CertEvent.EvMatchArm {
        scrutinee = scrutinee_se;
        adt_id = TypeDeclId.to_int adt_id;
        variant_id = VariantId.to_int variant_id;
        variant_name;
      })
  | Event.Binop { op; lhs; rhs; dst; result = _ } ->
      (match
         ( CertEvent.cert_place_of_place dst,
           CertEvent.cert_sym_expr_of_operand lhs,
           CertEvent.cert_sym_expr_of_operand rhs )
       with
       | Some cp, Some lhs_se, Some rhs_se ->
           Some (CertEvent.EvBinop {
             op = CertEvent.cert_binop_string op;
             lhs = lhs_se; rhs = rhs_se; dst = cp;
           })
       | _ -> None)
  | Event.Assign { dst; rvalue; value = _ } ->
      assign_to_cert ctx dst rvalue
  | Event.Call { fn; fn_name; call_id; args; arg_values; dst; region_abs } ->
      (* Translate operands / dest to cert payloads. Elide the event
         if any operand or the dest place doesn't lift — the
         original site did the same so the trace stays internally
         consistent. -*)
      let cert_args : CertEvent.cert_sym_expr list option =
        let xs = List.map CertEvent.cert_sym_expr_of_operand args in
        if List.for_all Option.is_some xs then Some (List.map Option.get xs)
        else None
      in
      let cert_dst : CertEvent.cert_place option =
        CertEvent.cert_place_of_place dst
      in
      (match cert_args, cert_dst with
       | Some args_e, Some dst_e ->
           (* M9.6 (Option C): build the per-abstraction abs_sig
              from the just-pushed abstractions visible in
              [ctx.env]. For each abs in [region_abs], walk its
              avalues and classify each aborrow/aloan content into
              an ArMutBorrow / ArMutLoan / ArSharedBorrow entry.
              [as_parent_abs] is the abs's ancestor set. -*)
           let arg_idx_of_loan : (BorrowId.id, int) Hashtbl.t =
             Hashtbl.create 8
           in
           List.iteri
             (fun i (arg : tvalue) ->
               let v = object
                 inherit [_] iter_tvalue as super
                 method! visit_VMutBorrow env bid mv =
                   if not (Hashtbl.mem arg_idx_of_loan bid) then
                     Hashtbl.add arg_idx_of_loan bid i;
                   super#visit_VMutBorrow env bid mv
                 method! visit_VSharedBorrow env bid sid =
                   if not (Hashtbl.mem arg_idx_of_loan bid) then
                     Hashtbl.add arg_idx_of_loan bid i;
                   super#visit_VSharedBorrow env bid sid
                 method! visit_VReservedMutBorrow env bid sid =
                   if not (Hashtbl.mem arg_idx_of_loan bid) then
                     Hashtbl.add arg_idx_of_loan bid i;
                   super#visit_VReservedMutBorrow env bid sid
               end in
               v#visit_tvalue () arg)
             arg_values;
           let abs_sig : CertEvent.cert_abs_shape list =
             List.filter_map
               (fun aid ->
                 match
                   List.find_opt
                     (fun e ->
                       match e with
                       | EAbs a when a.abs_id = aid -> true
                       | _ -> false)
                     ctx.env
                 with
                 | Some (EAbs abs) ->
                     let roles : CertEvent.cert_abs_role list ref = ref [] in
                     let v = object
                       inherit [_] iter_tavalue as super
                       method! visit_AMutBorrow env pm bid child =
                         let arg_idx =
                           try Hashtbl.find arg_idx_of_loan bid
                           with Not_found -> -1
                         in
                         roles :=
                           CertEvent.ArMutBorrow { arg_idx; loan = bid } :: !roles;
                         super#visit_AMutBorrow env pm bid child
                       method! visit_AMutLoan env pm lid child =
                         roles := CertEvent.ArMutLoan { loan = lid } :: !roles;
                         super#visit_AMutLoan env pm lid child
                       method! visit_ASharedBorrow env pm bid sid =
                         let arg_idx =
                           try Hashtbl.find arg_idx_of_loan bid
                           with Not_found -> -1
                         in
                         roles :=
                           CertEvent.ArSharedBorrow
                             { arg_idx; sb_id = sid }
                           :: !roles;
                         super#visit_ASharedBorrow env pm bid sid
                     end in
                     List.iter (fun av -> v#visit_tavalue () av) abs.avalues;
                     Some {
                       CertEvent.as_abs_id = aid;
                       as_parent_abs = AbsId.Set.elements abs.parents;
                       as_roles = List.rev !roles;
                     }
                 | _ -> None)
               region_abs
           in
           Some (CertEvent.EvCall {
             fn; fn_name; call_id;
             args = args_e;
             dst = dst_e;
             region_abs;
             abs_sig;
           })
       | _ -> None)
  | Event.Join { ctx_left; ctx_right; ctx_joined } ->
      let left_summary =
        CertEvent.cert_state_summary_of_env ctx_left.env
      in
      let right_summary =
        CertEvent.cert_state_summary_of_env ctx_right.env
      in
      let result_summary =
        CertEvent.cert_state_summary_of_env ctx_joined.env
      in
      (* M9.6 (Option C): per-result-env-local witness of which
         Fig. 11 rule the join algebra fired. Commit #10 shipped
         JoinSame / JoinSymbolic / JoinVar; commit #11 added the
         Collapse-Dup-MutBorrow case (JoinMutBorrows) and the
         ⊥-propagation cases (JoinBottomOther / JoinOtherBottom).
         For JoinMutBorrows.abs, we look up the new fresh borrow
         id in [ctx_joined]'s abstractions to find the owner;
         failing that, we record 0 (the Lean AbsRegistry
         validation rejects mismatched pairs). -*)
      let cert_witnesses : CertEvent.cert_join_entry list =
        let lookup env l =
          try Some (List.assoc l env) with Not_found -> None
        in
        let sym_expr_eq (a : CertEvent.cert_sym_expr)
            (b : CertEvent.cert_sym_expr) : bool = a = b
        in
        let is_sym_val (e : CertEvent.cert_sym_expr) :
            symbolic_value_id option =
          match e with SymVal sv -> Some sv | _ -> None
        in
        let is_sym_mut_borrow_tok (e : CertEvent.cert_sym_expr) :
            BorrowId.id option =
          match e with SymMutBorrowTok bid -> Some bid | _ -> None
        in
        let abs_of_borrow (bid : BorrowId.id) : AbsId.id option =
          let found = ref None in
          List.iter
            (fun (e : env_elem) ->
              match e with
              | EAbs abs ->
                let visitor = object
                  inherit [_] iter_tavalue as super
                  method! visit_AMutLoan env pm lid child =
                    if lid = bid && Option.is_none !found then
                      found := Some abs.abs_id;
                    super#visit_AMutLoan env pm lid child
                end in
                List.iter (fun av -> visitor#visit_tavalue () av)
                  abs.avalues
              | _ -> ())
            ctx_joined.env;
          !found
        in
        (* M10.x.0 (cert v6 #12): alongside each [cert_join_rule]
           witness we also emit a [cert_join_entry_delta]. The
           Lean replayer cross-checks the pair in [stepJoin]. -*)
        List.filter_map
          (fun (l, r_expr) ->
            let l_left = lookup left_summary.cs_env l in
            let l_right = lookup right_summary.cs_env l in
            match l_left, l_right with
            | Some le, Some re
              when sym_expr_eq le re && sym_expr_eq le r_expr ->
              Some
                CertEvent.{
                  je_local = l;
                  je_rule = JrJoinSame;
                  je_delta = JedTrivial;
                }
            | _, _ ->
              (* JoinMutBorrows (Collapse-Dup-MutBorrow). *)
              (match l_left, l_right, is_sym_mut_borrow_tok r_expr with
               | Some le, Some re, Some l_fresh
                 when (match is_sym_mut_borrow_tok le,
                             is_sym_mut_borrow_tok re with
                       | Some a, Some b -> a <> b
                       | _ -> false) ->
                 let l_l = Option.get (is_sym_mut_borrow_tok le) in
                 let l_r = Option.get (is_sym_mut_borrow_tok re) in
                 let abs_id =
                   match abs_of_borrow l_fresh with
                   | Some a -> a
                   | None -> AbsId.of_int 0
                 in
                 let abs : CertEvent.cert_abs_shape =
                   CertEvent.{
                     as_abs_id = abs_id;
                     as_parent_abs = [];
                     as_roles =
                       [ ArMutBorrow { arg_idx = 0; loan = l_l };
                         ArMutBorrow { arg_idx = 0; loan = l_r };
                         ArMutLoan { loan = l_fresh } ];
                   }
                 in
                 Some
                   CertEvent.{
                     je_local = l;
                     je_rule =
                       JrJoinMutBorrows
                         { l_left = l_l; l_right = l_r; l_fresh; abs };
                     je_delta = JedMutBorrows { l_fresh; abs_id };
                   }
               | _ ->
                 (match is_sym_val r_expr with
                  | Some sv
                    when (match l_left with
                          | Some le -> not (sym_expr_eq le r_expr)
                          | None -> true)
                      && (match l_right with
                          | Some re -> not (sym_expr_eq re r_expr)
                          | None -> true) ->
                    Some
                      CertEvent.{
                        je_local = l;
                        je_rule = JrJoinSymbolic sv;
                        je_delta = JedSymbolic sv;
                      }
                  | _ ->
                    (match l_left, l_right with
                     | Some _, Some _ ->
                       Some
                         CertEvent.{
                           je_local = l;
                           je_rule = JrJoinVar;
                           je_delta = JedTrivial;
                         }
                     | None, Some _ ->
                       let a0 = AbsId.of_int 0 in
                       Some
                         CertEvent.{
                           je_local = l;
                           je_rule = JrJoinBottomOther a0;
                           je_delta = JedBottomOther a0;
                         }
                     | Some _, None ->
                       let a0 = AbsId.of_int 0 in
                       Some
                         CertEvent.{
                           je_local = l;
                           je_rule = JrJoinOtherBottom a0;
                           je_delta = JedOtherBottom a0;
                         }
                     | None, None -> None))))
          result_summary.cs_env
      in
      Some (CertEvent.EvJoin {
        left = left_summary;
        right = right_summary;
        result = result_summary;
        witnesses = cert_witnesses;
      })
  | Event.LoopInv { loop_id; fp_env; input_abs_list } ->
      (* M9.6 (Option C): collect [(borrow_id, parent_abs_id)] pairs
         for every loop-introduced loan visible in the input abs
         list. Walk mirrors the original inline derivation at
         InterpLoops.ml. -*)
      let loan_registry : (BorrowId.id * AbsId.id) list =
        let acc = ref [] in
        List.iter
          (fun (abs : abs) ->
            let visitor = object
              inherit [_] iter_tavalue as super
              method! visit_AMutLoan env pm lid child =
                if not (List.mem_assoc lid !acc) then
                  acc := (lid, abs.abs_id) :: !acc;
                super#visit_AMutLoan env pm lid child
              method! visit_aproj_loans env apl =
                (* aproj_loans projects a symbolic value into the
                   abstraction's loan side; tolerated as a no-op
                   here for visitor symmetry with the original. -*)
                ignore apl.proj.sv_id;
                super#visit_aproj_loans env apl
            end in
            List.iter (fun av -> visitor#visit_tavalue () av) abs.avalues)
          input_abs_list;
        List.rev !acc
      in
      (* Push the loop onto the cert-side loop-id stack so any
         in-body [MutBorrow] event can derive
         [MbkLoopOwned loop_id]. Popped on [LoopEnd]. -*)
      ctx.cert_loop_id_stack := loop_id :: !(ctx.cert_loop_id_stack);
      Some (CertEvent.EvLoopInv {
        loop_id;
        invariant = CertEvent.cert_state_summary_of_env fp_env;
        loan_registry;
      })
  | Event.LoopEnd { loop_id } ->
      (* Pop the loop we just closed. -*)
      (match !(ctx.cert_loop_id_stack) with
       | _ :: rest -> ctx.cert_loop_id_stack := rest
       | [] -> ());
      Some (CertEvent.EvLoopEnd { loop_id })
  | Event.SymExpandMutBorrow
      { sv_id; bid; inner_sv; parent_abs; subst_locals; subst_loans } ->
      Some (CertEvent.EvSymExpandMutBorrow {
        sv_id; bid; inner_sv; parent_abs; subst_locals; subst_loans;
      })
  | Event.MutBorrow { loan; place; value } ->
      (match CertEvent.cert_place_of_place place with
       | Some cp ->
           let symval : symbolic_value_id =
             match value.value with
             | VSymbolic sv -> sv.sv_id
             | _ -> SymbolicValueId.of_int 0
           in
           (* M9.6 (Option C) — subsumes M9.5w + M9.5aa. Place
              projection contains a [Deref] ⇒ MbkInAbsReborrow (the
              caller-input abs owns the borrow's lifetime; absId is a
              placeholder until the AbsRegistry lands). No [Deref]
              but we're inside an open loop body ⇒ MbkLoopOwned with
              the topmost loop id from the cert loop stack.
              Otherwise ⇒ MbkDirect. *)
           let has_deref =
             List.exists
               (fun (pe : projection_elem) ->
                 match pe with Deref -> true | _ -> false)
               cp.cp_projection
           in
           let kind_hint : CertEvent.cert_mut_borrow_kind =
             if has_deref then
               CertEvent.MbkInAbsReborrow (AbsId.of_int 0)
             else
               match !(ctx.cert_loop_id_stack) with
               | top :: _ -> CertEvent.MbkLoopOwned top
               | [] -> CertEvent.MbkDirect
           in
           Some (CertEvent.EvMutBorrow {
             loan; place = cp; symval; kind_hint;
           })
       | None -> None)
  | _ ->
      (* Other variants are migrated in commits 4-9. *)
      None

let on_event (ctx : eval_ctx) (ev : Event.t) : unit =
  if !(ctx.cert_events_suppressed) then ()
  else
    match event_to_cert ctx ev with
    | None -> ()
    | Some cert_ev ->
        ctx.cert_event_buffer := cert_ev :: !(ctx.cert_event_buffer)

let observer : Observer.observer = { on_event }

let install () : unit = Observer.current := observer
