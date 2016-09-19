#!/bin/sh

this_exe_path=$(dirname "$0")
source "${this_exe_path}/include.sh"

if [ -z "$2" ]
then
  echo "Give input file, cutoff, and (optional) bfs depth." 1>&2
  exit 1
fi

xfilename=$1
cutoff=$2
bfs=$3

if [ -z "$bfs" ]
then
  bfs=1
fi

lines_per_exec=200

d=$(printf '%s' "$xfilename" | sed -e 's/^[^[:digit:]]*\([[:digit:]]*\).*$/\1/')
d=$(($d + $bfs))
bfs_ofilename="d${d}.${cutoff}.gz"
gen_ofilename="g${d}.${cutoff}.gz"

{
  zcat $xfilename \
  | parallel --pipe -n $lines_per_exec \
    "$gen_exe" -bfs $bfs -cutoff $cutoff -nw-disabling \
    -x-init - -o /dev/stderr \
  | gzip >$bfs_ofilename
} \
2>&1 \
| gzip >$gen_ofilename

