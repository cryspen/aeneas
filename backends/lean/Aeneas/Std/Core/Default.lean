module
public import Aeneas.Std.Primitives
public meta import Aeneas.Extract.Extract
public section

namespace Aeneas.Std

@[rust_trait "core::default::Default"]
structure core.default.Default (Self : Type u) where
  default : RustM Self

@[expose, rust_fun "core::default::{core::default::Default<bool>}::default"]
def core.default.DefaultBool.default : RustM Bool := .ok false

end Aeneas.Std
