#!/bin/sh

npcs=10

rm -f udp-host.*
rm -f out.log.*

for i in $(seq 0 $(expr $npcs - 1))
do
  ./udp $i $npcs 2>&1 | tee out.log.$i &
  #./udp $i $npcs 2>&1 &
done

for i in $(seq 0 $(expr $npcs - 1))
do
  wait
done

