#!/bin/sh

## This script removes duplicate protocol files.

pfx_a=match/v6.protocon
pfx_b=match/tmp/v7.protocon

for f in $pfx_a.*
do
  if [ ! -f "$f" ]
  then
    continue
  fi
  tmpf=`mktemp`
  sort "$f" > "$tmpf"
  for g in $(ls $pfx_b.*)
  do
    if sort "$g" | diff -q "$tmpf" - > /dev/null
    then
      echo $f $g
      rm $f $g
      break
    fi
  done
  rm "$tmpf"
done


