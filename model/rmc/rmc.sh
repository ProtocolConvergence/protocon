#!/bin/sh

rmc_pfx=$HOME/Downloads/rmc/usr

# --acceleration=tc

LD_LIBRARY_PATH="$rmc_pfx/lib" "$rmc_pfx/bin/rmc" "$@"
exit $?

