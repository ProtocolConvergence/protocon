#!/bin/sh

cd $(dirname "$0")

old_pathpfx="$1"
N="$2"
key="$3"
xfile="$old_pathpfx/$key.protocon"
logfile="log/verif${N}-${key}.log"

/usr/bin/time -f %e -- ../../bin/protocon -verify -def N "$N" -x "$xfile" \
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

