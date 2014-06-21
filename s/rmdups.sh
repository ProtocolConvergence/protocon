#!/bin/sh

## This script removes duplicate protocol files.

pfx=match/v6.protocon.
pfx=obliss/

for f in "$pfx"*
do
  if [ ! -f "$f" ]
  then
    continue
  fi
  tmpf=`mktemp`
  sort "$f" > "$tmpf"
  for g in $(ls "$pfx"* | grep -v $f)
  do
    if sort "$g" | diff -q "$tmpf" - > /dev/null
    then
      echo $f $g
      rm $g
    fi
  done
  rm "$tmpf"
done

