#!/bin/sh

#this_exe_path=$(dirname $(readlink -f "$0"))
this_exe_path=$(dirname "$0")
source "${this_exe_path}/include.sh"

threshold=$1
shift
filename=$1
shift
if [ -z "$threshold" -a -z "$filename" ]
then
  echo "Enter a threshold and filename." >&2
  exit 1
fi

tail -fn+0 "$filename" \
| parallel --pipe -n 20 -k \
  "${proj_path}/bld/uni/classify" $threshold -unknown

