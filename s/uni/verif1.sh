#!/bin/sh

this_exe_path=$(dirname $(readlink -f "$0"))
source "${this_exe_path}/include.sh"

if [ -n "$3" ]
then
  minsz=$1
  maxsz=$2
  key=$3
  shift 3
elif [ -n "$2" ]
then
  minsz=2
  maxsz=$1
  key=$2
  shift 2
else
  echo 'Need at least 2 arguments.' >&2
  exit 1
fi

protfile="/tmp/${key}.prot"
printf '%s' "$key" | "$xlate_exe" -o-prot "$protfile"
"${proj_path}/s/verifn.sh" "$minsz" "$maxsz" "$protfile" "$@"

ret=$?
rm "$protfile"

exit $ret

