#!/bin/sh
# Auto-generated reproducer for target `fork`.
# Fingerprint: Other extract/Extract.ml:2851
set -e
/Users/karthik/charon/charon/target/release/charon rustc --preset=aeneas --dest-file min.llbc -- --crate-type=rlib min.rs
/Users/karthik/aeneas/bin/aeneas -backend lean -abort-on-error -no-progress-bar min.llbc -dest out
