#!/bin/sh

proj_path=$(dirname $(readlink -f "$0"))
proj_path=$(dirname $(dirname "$proj_path"))
biring_exe="${proj_path}/biring"

old_name="$1"
new_name="$2"
idx=$(printf '%05u' $3)

cat "./log/${old_name}.${idx}" \
| grep -e "success" \
| sed -e 's/^\([01]*\) .*$/\1/' \
| "$biring_exe" -domsz 3 -xlate-invariant \
| xargs -n 2 -d '\n' "${proj_path}/s/biring/serialopt.sh" "$old_name" "$new_name" \
| tee "./log/${new_name}.${idx}" \
> /dev/null

