open Identifiers
open Meta
module SpecId = IdGen ()

(** The shape of an spec *)
type kind = | [@@deriving show]

type t = { id : SpecId.id; kind : kind; span : span option } [@@deriving show]
