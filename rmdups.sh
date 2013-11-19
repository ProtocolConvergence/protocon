#!/bin/sh

## This script removes duplicate protocol files.

pfx=kautz/v11.protocon

for f in $pfx.*
do
  if [ ! -f "$f" ]
  then
    continue
  fi
  for g in $(ls $pfx.* | grep -v $f)
  do
    if diff -q $f $g > /dev/null
    then
      echo $f $g
      rm $g
    fi
  done
done

