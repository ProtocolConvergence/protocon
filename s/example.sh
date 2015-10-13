#!/bin/sh

argsfile=$(dirname "$0")/../examplesett

name=$1
shift

if [ -z "$name" ]
then
  echo "Give an example name." 2>&1
  exit 1
fi

name=$(basename -s .args "$name")
name=$(basename -s .prot "$name")

argsfile="${argsfile}/${name}.args"

cmd=$(head -n 1 "$argsfile")
if [ 0 = $(expr match "$cmd" "^#!") ]
then
  cmd="protocon -x-args $argsfile"
else
  cmd=$(printf '%s' "$cmd" | sed -e 's/^#!//')
  cmd="$cmd $argsfile"
fi

exec $cmd "$@"

