open Identifiers
open Meta
module SpecId = IdGen ()

(** The shape of an entry — {b the extensible point}. One arm per shape. *)
type kind = HaxSpec of HaxSpecs.t [@@deriving show]

type t = { id : SpecId.id; kind : kind; span : span option } [@@deriving show]
