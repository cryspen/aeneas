(** Interpreter-native event vocabulary.

    Each variant corresponds to a single firing of an interpreter rule
    that downstream observers may want to watch. The payloads use
    interpreter-native types ([place], [tvalue], [borrow_id], etc.)
    only — there is intentionally no dependency on [CertEvent] or any
    other observer-side translation, so the cert pipeline is just
    *one* registered consumer.

    A maintainer adding a new interpreter rule writes one
    [Observer.notify] in interpreter vocabulary; they do not need to
    touch any observer code. -*)

open Types
open Values
open Expressions
open Contexts

type t =
  | MutBorrow of {
      loan : borrow_id;
      place : place;
      value : tvalue;
    }
      (** Fires when a fresh [&mut p] creates loan [loan] over [place]
          with the borrowed [value]. Observers extract whatever
          they need ([symbolic_value_id], cert kind_hint) from the
          tvalue and their own loop stack. -*)
  | SharedBorrow of {
      loan : borrow_id;
      sb_id : shared_borrow_id;
      place : place;
      value : tvalue;
    }
  | Assign of {
      dst : place;
      rvalue : rvalue;
      value : tvalue;
    }
  | Move of { src : place; dst : place }
  | Copy of { src : place; dst : place }
  | EndBorrow of {
      loan : borrow_id;
      borrowed_value : tvalue option;
          (** [Some bv] when the underlying [borrow_content] is
              [Concrete (VMutBorrow (_, bv))]; [None] otherwise.
              Observers extract the cert-side [given_back] expression
              from [bv] or fall back to a loan-token reference when
              [None]. The observer fires *pre*-[give_back_concrete] so
              the [VMutLoan loan] holder is still in [ctx.env]. -*)
    }
  | Assert of { cond_value : tvalue; expected : bool }
  | Panic
  | Return
  | Binop of {
      op : binop;
      lhs : operand;
      rhs : operand;
      dst : place;
      result : tvalue;
    }
  | Reborrow of {
      child : borrow_id;
      parent : borrow_id;
      place : place;
      parent_live : bool;
      parent_abs : abs_id option;
    }
  | Call of {
      fn : fun_decl_id;
      fn_name : string;
      call_id : fun_call_id;
      args : operand list;
      arg_values : tvalue list;
      dst : place;
      region_abs : abs_id list;
      freshened_abs : abs list;
          (** The abstractions freshly minted by this call. Observers
              walk these to derive cert-side role / shape data. -*)
    }
  | EndAbs of {
      abs_id : abs_id;
      abs_value : abs option;
          (** [Some abs] when the abs is still in the context at
              emit-time (just after [end_abs_borrows] replaced its
              [AMutBorrow] / [AProjBorrows] entries with the
              [AEnded*] forms); [None] when the lookup failed (the
              original site emitted an event with empty payload). -*)
      pre_end_env : env;
          (** Snapshot of [ctx.env] captured at the top of
              [end_abs_aux], before any sub-loan ends substituted the
              [VMutLoan] tokens. Observers walk this to derive
              [token_clear_locals]; the live [ctx.env] at observer-fire
              time has already had those tokens rewritten. -*)
    }
  | SymExpandMutBorrow of {
      sv_id : symbolic_value_id;
      bid : borrow_id;
      inner_sv : symbolic_value_id;
      parent_abs : abs_id option;
      subst_locals : local_id list;
      subst_loans : borrow_id list;
    }
  | Join of {
      ctx_left : eval_ctx;
      ctx_right : eval_ctx;
      ctx_joined : eval_ctx;
    }
      (** A join over two branch contexts. Observers re-derive any
          [cert_state_summary] / witness data from the three [eval_ctx]
          slices. -*)
  | LoopInv of {
      loop_id : loop_id;
      fp_env : env;
      input_abs_list : abs list;
          (** The loop's input abstractions (filtered from
              [fp_ctx.env]). Observers walk these to build the cert
              loan registry. -*)
    }
      (** Start of a loop body's canonical synthesis. Observers also
          push [loop_id] onto their loop-id stack here (popped on
          [LoopEnd]) so in-body [MutBorrow] events can derive
          [MbkLoopOwned]. -*)
  | LoopEnd of { loop_id : loop_id }
  | MatchArm of {
      scrutinee : tvalue;
      adt_id : type_decl_id;
      variant_id : variant_id;
      variant_name : string;
    }
