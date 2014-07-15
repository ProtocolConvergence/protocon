#!/bin/sh

old_sfx="$1"
N="$2"
new_sfx="verif$N"
old_pathpfx="$old_sfx"
idx=$(printf '%05u' $3)

cat "./log/summary$old_sfx.log.$idx" \
| grep -e "success" \
| sed -e 's/^\([01]*\) .*$/\1/' \
| xargs -n 1 -d '\n' ./serialverif.sh "$old_pathpfx" "$N" \
| tee "log/summary$new_sfx.log.$idx" \
> /dev/null

