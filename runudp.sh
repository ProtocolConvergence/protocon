#!/bin/sh

npcs=50

rm -f udp-host.*
rm -f out.log.*

for i in $(seq 0 $(expr $npcs - 1))
do
  ./udp $i $npcs out.log.$i 2>&1 &
  #valgrind --track-origins=yes ./udp $i $npcs out.log.$i 2>&1 &
  #./udp $i $npcs 2>&1 | tee out.log.$i &
  #./udp $i $npcs 2>&1 &
done

for i in $(seq 0 $(expr $npcs - 1))
do
  wait
done

