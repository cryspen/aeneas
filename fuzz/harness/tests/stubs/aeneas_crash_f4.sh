#!/bin/sh
# Stub aeneas: reproduces the F4 crash signature.
#   [Error] + Compiler source -> STDOUT
#   Uncaught exception + backtrace -> STDERR
# Exit code 2 (crash).
cat <<'EOF'
[Info ] Imported: crate.llbc
[Error] Internal error, please file an issue
Source: 'lib.rs', lines 1:0-3:1
Compiler source: pure/PureMicroPassesLoops.ml, line 1818
EOF
cat >&2 <<'EOF'
Uncaught exception:
  (Failure "Internal error, please file an issue")
Raised at Aeneas__Errors.craise_opt_span in file "Errors.ml", line 120, characters 4-23
Called from Aeneas__PureMicroPassesLoops.reorder_loop_outputs.update_and_close_loop_body.upd in file "pure/PureMicroPassesLoops.ml", lines 1818-1819, characters 18-67
Called from Aeneas__PureMicroPassesLoops.reorder_loop_outputs.explore in file "pure/PureMicroPassesLoops.ml", lines 2205-2206, characters 22-45
EOF
exit 2
