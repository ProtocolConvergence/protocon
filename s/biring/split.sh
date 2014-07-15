#!/bin/sh

f=$1
n=$2

function splitit
{
  sort -R "$f" \
  | split --verbose -l $n -d -a 5 - "$f." \
  | wc -l
}

count=$(printf '%05u' $(splitit))
mv $f.00000 $f.$count

