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
      given_back : tvalue;
      holder_local : local_id option;
          (** The local that holds the [VMutLoan loan] at the moment
              the loan ends. Computed *pre*-[give_back_concrete] by
              the emit site; the observer cannot recompute this
              post-fact (the loan binding has been rewritten). -*)
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
      abs : abs;
      final_values : tvalue list;
      released_loans : borrow_id list;
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
      fp_ctx : eval_ctx;
    }
      (** Start of a loop body's canonical synthesis. The fixpoint
          context [fp_ctx] carries the loan registry observers need to
          walk. -*)
  | LoopEnd of { loop_id : loop_id }
  | MatchArm of {
      scrutinee : tvalue;
      adt_id : type_decl_id;
      variant_id : variant_id;
      variant_name : string;
    }
