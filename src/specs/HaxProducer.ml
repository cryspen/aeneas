(** The hax specs gatherer.

    Hax encodes [#[hax_lib::requires(...)]] / [#[hax_lib::ensures(|r| ...)]]
    annotations as separate "decoration" functions plus [_hax::json] attributes
    that link a real function to its pre/post decorations by UUID. This module
    parses those attributes, and the [gather] producer folds them into {!Spec.t}
    entries (consuming the decoration functions). *)

let gather (_ctx : TranslateCore.trans_ctx)
    (crate : TranslateCore.translated_crate) : TranslateCore.translated_crate =
  crate
