#!/bin/sh

metapath=$(dirname "$0")

toppath="$metapath/../../"
distpath=$1

if [ ! "$distpath" ]
then
  distpath="$toppath/protocon-bin"
fi

mkdir -p "$distpath/bin"
cp -a -t "$distpath/bin" "$toppath/bin/protocon" "$toppath/bin/protocon-gui" "$toppath/bin/protocon-mpi"

mkdir -p "$distpath/inst"
cat "$metapath/inst.files" | \
{
  while read
  do
    cp -a -t "$distpath/inst" "$toppath/protocon/inst/$REPLY"
  done
}

mkdir -p "$distpath/inst-stabilizing"
cat "$metapath/inst-stabilizing.files" | \
{
  while read
  do
    cp -a -t "$distpath/inst-stabilizing" "$toppath/protocon/inst-stabilizing/$REPLY"
  done
}

mkdir -p "$distpath/doc"
cp -a -t "$distpath/doc" "$toppath/protocon/doc/protocon.1"

