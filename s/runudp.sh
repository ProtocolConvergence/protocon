#!/bin/sh

npcs=$1

if [ ! "$npcs" ]
then
  echo "Give a number of processes!"
  exit 1
fi

ExeName=$(readlink -f "$0")
udp=$(dirname $(dirname "$ExeName"))/src/udp

rm -f udp-host.*
rm -f out.log.*
rm -f pids

for i in $(seq 0 $(expr $npcs - 1))
do
  "$udp" $i $npcs out.log.$i 2>&1 &
  echo $! >> pids
  #valgrind --track-origins=yes "$udp" $i $npcs out.log.$i 2>&1 &
  #"$udp" $i $npcs 2>&1 | tee out.log.$i &
  #"$udp" $i $npcs 2>&1 &
done

for i in $(seq 0 $(expr $npcs - 1))
do
  wait
done

rm -f pids

