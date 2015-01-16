#!/bin/sh

beg=$1
shift
end=$1
shift
f=$1
shift

for N in `seq $beg $end`
do
  protocon -verify -x "$f" -def N $N "$@"
  stat=$?
  if [ $stat -ne 0 ]
  then
    echo "Failed on N=$N, status $stat" >&2
    exit $stat
  fi
done

exit 0

