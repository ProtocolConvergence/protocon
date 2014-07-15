#!/bin/sh

cd $(dirname "$0")

old_sfx="$1"
new_sfx="$2"
old_pathpfx="$old_sfx"
new_pathpfx="$new_sfx"
idx=$(printf '%05u' $3)

cat "./log/summary$old_sfx.log.$idx" \
| grep -e "success" \
| sed -e 's/^\([01]*\) .*$/\1/' \
| "$HOME/code/cx/protocon/biring" -xlate-invariant 3 -echo-bittable \
| xargs -n 2 -d '\n' ./serialopt.sh "$old_pathpfx" "$new_pathpfx" \
| tee "log/summary$new_sfx.log.$idx" \
> /dev/null

