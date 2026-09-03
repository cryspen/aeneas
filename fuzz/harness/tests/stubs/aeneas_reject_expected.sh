#!/bin/sh
# Stub aeneas: a clean, expected feature-gate rejection (message on STDOUT, no
# backtrace). Exit 1.
echo "[Error] Nested borrows are not supported yet"
echo "Source: 'lib.rs', lines 1:0-1:20"
exit 1
