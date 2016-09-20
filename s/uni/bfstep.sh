#!/bin/sh

this_exe_path=$(dirname "$0")
source "${this_exe_path}/include.sh"

xfilename=$1
shift
cutoff=$1
shift
bfs=$1
shift
dfs_threshold=$1
shift

if [ -z "$cutoff" ]
then
  echo "Give input file, cutoff, (optional) bfs depth, and (optional) dfs threshold." 1>&2
  exit 1
fi

if [ -z "$bfs" ]
then
  bfs=1
fi

if [ -z "$dfs_threshold" ]
then
  dfs_threshold=10
fi

lines_per_exec=200

d=$(printf '%s' "$xfilename" | sed -e 's/^[^[:digit:]]*\([[:digit:]]*\).*$/\1/')
d=$(($d + $bfs))
bfs_ofilename="d${d}.${cutoff}.gz"
gen_ofilename="g${d}.${cutoff}.gz"

{
  zcat $xfilename \
  | parallel --pipe -n $lines_per_exec \
    "$gen_exe" -nw-disabling -cutoff $cutoff \
    -bfs $bfs -dfs-within $dfs_threshold \
    -flushoff -trustme \
    "$@" \
    -x-init - -o /dev/stderr \
  | gzip >$bfs_ofilename
} \
2>&1 \
| gzip >$gen_ofilename

