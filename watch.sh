#!/bin/sh

tmpf=tmp
logf=out.log
npcs=2

while true
do
  {
    echo '------------------------------------'
    for i in $(seq 0 $(expr $npcs - 1))
    do
      tail -n3 $logf.$i
      echo -n '\___'
      ls --full-time $logf.$i
    done
    echo -n '\___'
  } >$tmpf
  ls --full-time $tmpf >> $tmpf
  cat $tmpf
  sleep 1
done

