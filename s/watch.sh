#!/bin/sh

nlines=10
logf=out.log
if [ "$1" ]
then
  logf=$1
fi

tmpf=$logf.tmp

while true
do
  {
    echo '------------------------------------------------------------------------------'
    for f in "$logf"*
    do
      if [ "$f" = "$tmpf" ]
      then
        continue
      fi
      tail -n $nlines "$f"
      echo -n '\___'
      ls --full-time "$f"
    done
    echo -n '\___'
  } >$tmpf
  ls --full-time "$tmpf" >> "$tmpf"
  cat "$tmpf"
  rm -f "$tmpf"
  sleep 1
done

