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

mkdir -p "$distpath/examplespec"
cat "$metapath/examplespec.files" | \
{
  while read f
  do
    cp -a -t "$distpath/examplespec" "$toppath/protocon/examplespec/$f.protocon"
  done
}

mkdir -p "$distpath/examplesoln"
cat "$metapath/examplesoln.files" | \
{
  while read f
  do
    cp -a -t "$distpath/examplesoln" "$toppath/protocon/examplesoln/$f.protocon"
  done
}

mkdir -p "$distpath/doc"
cp -a -t "$distpath/doc" "$toppath/protocon/doc/protocon.1"

