#!/bin/sh

FixedHostname=127.0.0.1
#FixedHostname=10.0.0.1

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
Ex #1: Run InputFile.prot with N=5 processes and M=4.
  $ExeName InputFile.prot 5 -def M 4"
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
  udp=$(dirname $(dirname "$ExePath"))/bld/src/udp-impl/udp_ThreeColorRing
else
  protfile=$1
  shift
  npcs=$1
  shift
  vital protocon -nop "$@" -x "$protfile" -def N $npcs -o-udp udp.c
  vital gcc -DFixedHostname=\""$FixedHostname"\" udp.c -o udp -lrt
fi

rm -f udp-host.*
rm -f out.log.*
rm -f pids

for i in $(seq 0 $(expr $npcs - 1))
do
  cmd="$udp $i"
  if empty_ck "$protfile"; then
    cmd="$cmd $npcs"
  fi
  cmd="$cmd -o-log out.log.$i"

  $cmd 2>&1 &
  #valgrind --track-origins=yes $cmd 2>&1 &
  echo $! >> pids
done

for i in $(seq 0 $(expr $npcs - 1))
do
  wait
done

rm -f pids

