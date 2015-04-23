#!/bin/sh

metapath=$(dirname $(readlink -f "$0"))
srcpath=$(dirname "$metapath")
toppath=$(dirname "$srcpath")
src=protocon

source "$metapath/include.sh"
init_distpath "$1" "$toppath/protocon-src"

mkdir -p "$distpath"
cd "$distpath"
git clone --depth=1 "file://$toppath/cx" cx
rm -fr cx/.git
git clone --depth=1 "file://$toppath/cx-pp" cx-pp
rm -fr cx-pp/.git
git clone --depth=1 "file://$toppath/protocon" $src
rm -fr $src/.git $src/.gitignore $src/.vimrc

cp -a -t ./ "$metapath/CMakeLists.txt"
rm -f cx/Makefile.raw
rm -f $src/Makefile.raw

copy_examples
rm -fr "$src/examplespec" "$src/examplesynt" "$src/examplesoln"

rm -fr $src/verif

rm -fr $src/meta
mv $src/doc doc
make_doc .

zip_up

