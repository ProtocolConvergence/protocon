#!/bin/sh

key=$1
path=/tmp
proj_path=$(dirname $(readlink -f "$0"))
proj_path=$(dirname $(dirname "$proj_path"))
biring_exe="${proj_path}/biring"

echo "$key" \
| "${biring_exe}" -o-graphviz "${path}/${key}.dot" \
>/dev/null

dot -Tpdf < "${path}/${key}.dot" > "${path}/${key}.pdf"

rm -f "${path}/${key}.dot"
echo "see ${path}/${key}.pdf"
see "${path}/${key}.pdf"
rm -f "${path}/${key}.pdf"


