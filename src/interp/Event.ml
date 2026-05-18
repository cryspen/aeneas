open Types
open Values
open Expressions
open Contexts

type t =
  | MutBorrow of {
      loan : borrow_id;
      place : place;
      symval : symbolic_value;
    }
  | SharedBorrow of {
      loan : borrow_id;
      sb_id : shared_borrow_id;
      place : place;
      symval : symbolic_value;
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
  | LoopInv of {
      loop_id : loop_id;
      fp_ctx : eval_ctx;
    }
  | LoopEnd of { loop_id : loop_id }
  | MatchArm of {
      scrutinee : tvalue;
      adt_id : type_decl_id;
      variant_id : variant_id;
      variant_name : string;
    }
