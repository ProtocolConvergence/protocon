#!/bin/sh

metapath=$(readlink -f $(dirname "$0"))
srcpath=$(dirname "$metapath")
toppath=$(dirname "$srcpath")
src=protocon

distpath=$1

if [ ! "$distpath" ]
then
  distpath="$toppath/protocon-src"
fi

distpath=$(readlink -f "$distpath")

if ! make -C $srcpath/doc
then
  echo 'Cannot create documentation.' >&2
  exit 1
fi

mkdir -p "$distpath"
cd "$distpath"
git clone --depth=1 "$toppath/cx" cx
rm -fr cx/.git
git clone --depth=1 "$toppath/cx-pp" cx-pp
rm -fr cx-pp/.git
git clone --depth=1 "$toppath/protocon" $src
rm -fr $src/.git

cp -a -t ./ "$metapath/CMakeLists.txt"
rm -f cx/Makefile.raw
rm -f $src/Makefile.raw

mkdir -p "examplespec"
cat "$metapath/examplespec.files" | \
{
  while read f
  do
    cp -a -t examplespec "$srcpath/examplespec/$f.protocon"
  done
}
rm -fr $src/examplespec

mkdir -p "examplesoln"
cat "$metapath/examplesoln.files" | \
{
  while read f
  do
    cp -a -t examplesoln "$srcpath/examplesoln/$f.protocon"
  done
}
rm -fr $src/examplesoln

rm -fr $src/verif/include.cmake

rm -fr $src/meta
mv $src/doc doc

cd "$(dirname "$distpath")"
distname=$(basename "$distpath")
tar czf "$distname.tar.gz" "$distname"
chmod a+r,a-x "$distname.tar.gz"

