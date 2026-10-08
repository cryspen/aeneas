(** The Hax spec-objects

    Hax_lib macros allow for specs written directly in rust. This module
    provides type definitions to represent such specs: pre/post on functions,
    and trait contracts with the impl obligations they induce. *)

(** Type for spec objects *)
type spec =
  | FunctionSpec of function_spec
  | TraitSpec of trait_spec
      (** The contract of a trait: its [X.Lawful] structure and the conditions
          of its annotated methods *)
[@@deriving show]

and function_spec = {
  fn : Pure.FunDeclId.id;
  pre : Pure.fun_decl option;  (** Precondition *)
  post : Pure.fun_decl option;  (** Postcondition *)
}
[@@deriving show]

(** The contract of a local trait. The producer emits one per local trait,
    possibly with no [methods] ([X.Lawful] then only has the parent fields, if
    any). The parents, generics and method signatures are read from the
    {!Pure.trait_decl}. *)
and trait_spec = {
  trait_decl : Pure.TraitDeclId.id;
  methods : method_spec list;  (** The annotated methods, in declaration order *)
}
[@@deriving show]

(** The contract of an annotated trait method (required or provided) *)
and method_spec = {
  method_id : Pure.trait_method_id;
  pre : Pure.fun_decl option;  (** Precondition *)
  post : Pure.fun_decl option;  (** Postcondition *)
}
[@@deriving show]

(** Type for proof-obligation objects. *)
and obligation =
  | FunctionContract of { spec : function_spec; proof : proof }
  | ImplLawful of {
      impl : Pure.TraitImplId.id;
      spec : trait_spec option;
          (** The contract of the implemented trait. [None] for a non-local
              trait: its [Lawful] fields are only known on the Lean side, so the
              obligation gets no field skeleton. *)
      proof : proof;
    }
      (** [<impl>.Lawful : X.Lawful … <impl>]: the impl satisfies the contract
          of its trait *)
[@@deriving show]

(** Type for proof objects *)
and proof = Admitted [@@deriving show]

(** The extra Lean modules hax specs need to elaborate *)
let required_imports () : string list = [ "Hax" ]
