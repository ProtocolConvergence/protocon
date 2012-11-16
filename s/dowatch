#!/bin/sh

cmd="$1"
if [ -z "$cmd" ]
then
  printf 'Usage: %s COMMAND FILE [FILE]*\n' $0 >&2
  echo "  Run COMMAND when any of the files change." >&2
  exit 1
fi
shift

oldkey=""
while true
do
  newkey=`ls --full-time "$@"`
  if [ "$newkey" != "$oldkey" ]
  then
    printf '\n\n\n\n\n\n\n\n\n\n' >&2
    printf 'Running: sh -c "%s"\n' "$cmd" >&2
    sleep 1
    newkey=`ls --full-time "$@"`
    sh -c "$cmd"
    printf 'Result was: %d\n' $? >&2
  fi
  oldkey=$newkey
  sleep 1
done

