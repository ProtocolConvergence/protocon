#!/bin/sh

metapath=$(readlink -f $(dirname "$0"))
srcpath=$(dirname "$metapath")
toppath=$(dirname "$srcpath")
distpath=$1

if [ ! "$distpath" ]
then
  distpath="$toppath/protocon-bin"
fi

distpath=$(readlink -f "$distpath")

if ! make -C "$srcpath/doc"
then
  echo 'Cannot create documentation.' >&2
  exit 1
fi

mkdir -p "$distpath/bin"
cp -a -t "$distpath/bin" "$toppath/bin/protocon" "$toppath/bin/protocon-gui" "$toppath/bin/protocon-mpi"

mkdir -p "$distpath/examplespec"
cat "$metapath/examplespec.files" | \
{
  while read f
  do
    cp -a -t "$distpath/examplespec" "$toppath/protocon/examplespec/$f.prot"
  done
}

mkdir -p "$distpath/examplesoln"
cat "$metapath/examplesoln.files" | \
{
  while read f
  do
    cp -a -t "$distpath/examplesoln" "$toppath/protocon/examplesoln/$f.prot"
  done
}

cp -a -t "$distpath" "$srcpath/doc"
rm -fr "$distpath/doc/webtex"
rm -f "$distpath/doc/Makefile"

cd "$(dirname "$distpath")"
distname=$(basename "$distpath")
tar czf "$distname.tar.gz" "$distname"
chmod a+r,a-x "$distname.tar.gz"

