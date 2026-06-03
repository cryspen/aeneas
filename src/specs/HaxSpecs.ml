(** The Hax spec-objects

    Hax_lib macros allow for specs written directly in rust. This module
    provides type definitions to represent such specs. Currently, it supports
    only pre/post on standalone functions. *)

(** Type for spec objects *)
type t =
  | FunctionSpec of {
      fn : Pure.FunDeclId.id;  (** Precondition *)
      pre : Pure.fun_decl option;  (** Postcondition *)
      post : Pure.fun_decl option;
      proof : proof;
    }
[@@deriving show]

(** Type for proof objects *)
and proof = Admitted [@@deriving show]
