import AeneasCheck.Raw.CertEvent
import AeneasCheck.Raw.LLBCProgram
import AeneasCheck.Json.Parser
import AeneasCheck.Typecheck.Types
import AeneasCheck.Typecheck.Consistency
import AeneasCheck.LLBCSharp.Replay
import AeneasCheck.Pure.Pretty
import AeneasCheck.Translate.Driver
import AeneasCheck.Translate.LlbcTrusted
import AeneasCheck.Backends.RustEmit

/-!
Top-level module for the Aeneas Lean checker.

The checker takes a Charon-produced LLBC + an Aeneas-produced cert
(format defined in `src/cert/cert_schema.json`), replays the LLBC#
trace deterministically against the program, and translates the
result to a Pure IR that can be emitted as a Rust model (for
differential testing). The Lean-emit backend was retired in Phase 2a;
only the verified replayer + the Rust-model emit remain.

Trust boundary: this checker plus the Lean kernel are the TCB for any
proof done over its output. The OCaml symbolic interpreter is
untrusted — if the cert lies, the checker rejects it.
-/

namespace AeneasCheck

/-- Library version. Bump when changing public API. -/
def version : String := "0.1.0-dev"

end AeneasCheck
