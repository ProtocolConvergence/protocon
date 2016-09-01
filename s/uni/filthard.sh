#!/bin/sh

this_exe_path=$(dirname $(readlink -f "$0"))
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

tail -fn+0 "$filename" |
while read line
do
  domsz=$(calc_domsz "$line")
  echo $line |
  "${proj_path}/bld/uni/generate" -domsz $domsz -o-list - |
  "${proj_path}/bld/uni/classify" $threshold |
  tee /dev/stderr |
  grep unknown |
  sed "s/.*/$line/"
done

