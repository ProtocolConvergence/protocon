#!/bin/sh

proj_path=$(dirname $(readlink -f "$0"))
proj_path=$(dirname $(dirname "$proj_path"))

old_name="$1"
N="$2"
new_name="verif$N"
idx=$(printf '%05u' $3)

cat "./log/${old_name}.${idx}" \
| grep -e "success" \
| sed -e 's/^\([01]*\) .*$/\1/' \
| xargs -n 1 -d '\n' "${proj_path}/s/biring/serialverif.sh" "$old_name" "$N" \
| tee "log/${new_name}.${idx}" \
> /dev/null

