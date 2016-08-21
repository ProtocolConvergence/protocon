#!/bin/sh

this_exe_path=$(dirname $(readlink -f "$0"))
source "${this_exe_path}/include.sh"

key=$1
shift
domsz=$(calc_domsz "$key")

path=/tmp
echo "$key" \
| "${gen_exe}" -domsz "$domsz" -o-graphviz "${path}/${key}.dot"

dot -Tpng < "${path}/${key}.dot" > "${path}/${key}.png"

rm "${path}/${key}.dot"
echo "see ${path}/${key}.png"
see "${path}/${key}.png"
rm "${path}/${key}.png"


