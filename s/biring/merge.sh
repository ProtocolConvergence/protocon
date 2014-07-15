#!/bin/sh

f=$1

cat $f.* \
| sort -n -r  > $f

rm -f $f.*

