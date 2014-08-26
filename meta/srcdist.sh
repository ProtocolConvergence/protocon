#!/bin/sh

metapath=$(readlink -f $(dirname "$0"))
srcpath=$(dirname "$metapath")
toppath=$(dirname "$srcpath")

distpath=$1

if [ ! "$distpath" ]
then
  distpath="$toppath/protocon-src"
fi

mkdir -p "$distpath"
cd "$distpath"
git clone "$toppath/cx" cx
rm -fr cx/.git
git clone "$toppath/cx-pp" cx-pp
rm -fr cx-pp/.git
git clone "$toppath/protocon" src
rm -fr src/.git

cp -a "$metapath/src-top-Makefile" Makefile
rm -f cx/Makefile.raw
rm -f src/Makefile.raw

mkdir -p "examplespec"
cat "$metapath/examplespec.files" | \
{
  while read f
  do
    cp -a -t examplespec "$srcpath/examplespec/$f"
    #mv "src/examplespec/$f" examplespec
  done
}
rm -fr src/examplespec

mkdir -p "examplesoln"
cat "$metapath/examplesoln.files" | \
{
  while read f
  do
    cp -a -t examplesoln "$srcpath/examplesoln/$f"
    #mv "src/examplesoln/$f" examplesoln
  done
}
rm -fr src/examplesoln

rm -fr src/meta
mv src/doc doc

