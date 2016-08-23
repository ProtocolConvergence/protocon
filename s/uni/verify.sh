#!/bin/sh

this_exe_path=$(dirname $(readlink -f "$0"))
source "${this_exe_path}/include.sh"

if [ $# -gt 2 ]
then
  use_args=1
  arg1="$1"
  arg2="$2"
  shift 2
else
  use_args=""
fi

while read line
do
  if [ -z "$use_args" ]
  then
    "${this_exe_path}/verif1.sh" "$@" "$line" >/dev/null 2>&1
    istat=$?
  else
    "${this_exe_path}/verif1.sh" "$arg1" "$arg2" "$line" "$@" >/dev/null 2>&1
    istat=$?
  fi
  if [ $istat -eq 0 ]
  then
    printf 'SUCCESS %s\n' "$line"
  else
    printf 'FAILURE %s\n' "$line"
  fi
done

