#!/bin/sh

function eq ()
{
  return $(expr + "$1" != + "$2")
}

function empty_ck ()
{
  eq "" "$1"
  return $?
}

vital()
{
  echo "$@" >&2
  if ! "$@"
  then
    exit 1
  fi
}

udp=./udp

if empty_ck "$1"
then
  ExeName=udp.sh
cat 1>&2 <<HERE
Example usages:
Ex #1: Run InputFile.prot with 5 processes.
  $ExeName InputFile.prot -def N 5"
Ex #2: Run the default udp program with 5 processes.
  $ExeName -- 5
HERE
  exit 1
fi

protfile=

if eq -- "$1"
then
  shift
  npcs=$1
  shift
  ExePath=$(readlink -f "$0")
  udp=$(dirname $(dirname "$ExePath"))/src/udp
else
  protfile=$1
  shift
  npcs=$1
  shift
  vital protocon -nop -def N $npcs "$@" -x "$protfile" -o-udp udp.c
  vital gcc udp.c -o udp -lrt
fi

rm -f udp-host.*
rm -f out.log.*
rm -f pids

for i in $(seq 0 $(expr $npcs - 1))
do
  arg2=
  if empty_ck "$protfile"; then
    arg2=$npcs
  fi
  "$udp" $i $arg2 -o-log out.log.$i 2>&1 &
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

