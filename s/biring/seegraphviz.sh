#!/bin/sh

key=$1
M=3
path=/tmp
proj_path=$(dirname $(readlink -f "$0"))
proj_path=$(dirname $(dirname "$proj_path"))
biring_exe="${proj_path}/bld/biring"

echo "$key" \
| "${biring_exe}" -echo -domsz $M -o-graphviz "${path}/${key}.dot"

dot -Tpng < "${path}/${key}.dot" > "${path}/${key}.png"

rm "${path}/${key}.dot"
echo "see ${path}/${key}.png"
see "${path}/${key}.png"
rm "${path}/${key}.png"


