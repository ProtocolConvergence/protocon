#!/bin/sh

this_exe_path=$(dirname $(readlink -f "$0"))
source "${this_exe_path}/include.sh"

key=$1
shift

path=/tmp
echo "$key" \
| "${gen_exe}" -o-graphviz "${path}/${key}.dot"

dot -Tpng < "${path}/${key}.dot" > "${path}/${key}.png"

rm "${path}/${key}.dot"
echo "see ${path}/${key}.png"
see "${path}/${key}.png"
rm "${path}/${key}.png"


