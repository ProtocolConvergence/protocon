#!/bin/sh

# Each line of input and output have the form:
#  <status>\t<key>
# where <status> is "silent", "livelock", or "unknown".
# and <key> is the bit vector for a set of actions.
# Lines that are not "unknown" are discarded.

this_exe_path=$(dirname $(readlink -f "$0"))
source "${this_exe_path}/include.sh"

if [ -z "$1" ]
then
  echo "Usage: $0 <max-period>" >&2
  exit 1
fi
max_period="$1"

grep 'unknown' \
| cut -f 2 \
| \
while read bt
do
  result=$(printf '%s' "$bt" | "${gen_exe}" -verify -max-period "$max_period")
  printf '%s\t%s\n' "$result" "$bt"
done

