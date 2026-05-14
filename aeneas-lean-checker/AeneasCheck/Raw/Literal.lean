import AeneasCheck.Raw.Types

namespace AeneasCheck.Raw

/--
Raw literal value matching the cert.json `literal` shape. We carry
scalars as `Int` because all integers in the direct-borrow subset fit
comfortably; M9+ swaps to `BigInt` if needed (the schema already
serializes scalars as strings to keep the format width-agnostic).
-/
inductive Lit
  | scalar (k : IntKind) (v : Int)
  | bool (b : Bool)
  | char (c : Nat)
  | str (s : String)
  | byteStr (bs : Array Nat)
  deriving Repr, BEq

end AeneasCheck.Raw
