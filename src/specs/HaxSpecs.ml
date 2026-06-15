(** The Hax spec-objects

    Hax_lib macros allow for specs written directly in rust. This module
    provides type definitions to represent such specs. Currently, it supports
    only pre/post on standalone functions. *)

(** Type for spec objects *)
type spec = FunctionSpec of function_spec [@@deriving show]

and function_spec = {
  fn : Pure.FunDeclId.id;
  pre : Pure.fun_decl option;  (** Precondition *)
  post : Pure.fun_decl option;  (** Postcondition *)
}
[@@deriving show]

(** Type for proof-obligation objects (mirrors {!specs}). *)
and obligation = FunctionContract of { spec : function_spec; proof : proof }
[@@deriving show]

(** Type for proof objects *)
and proof = Admitted [@@deriving show]
