#!/bin/sh

proj_path=$(dirname $(readlink -f "$0"))
proj_path=$(dirname $(dirname "$proj_path"))
protocon_exe="${proj_path}/../bin/protocon"

old_name="$1"
N="$2"
key="$3"
xfile="${old_name}/${key}.protocon"
logfile="log/verif${N}-${key}.log"

/usr/bin/time -f %e -- "$protocon_exe" -verify -def N "$N" -x "$xfile" \
1>"$logfile" 2>&1

retcode=$?

nlayers=$(grep "async layers" "$logfile" | sed -e 's/^.* //')
nsecs=$(tail -n 1 "$logfile")

if [ $retcode -eq 0 ]
then
  echo "$key" success "$nlayers" "$nsecs"
else
  echo "$key" failure "$nlayers" "$nsecs"
fi

rm -f "$logfile"

