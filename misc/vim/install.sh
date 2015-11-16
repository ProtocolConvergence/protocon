#!/bin/sh

ExePath=$(readlink -f "$0")

srcpath=$(dirname "$ExePath")
dstpath=${HOME}/.vim

mkdir -p "$dstpath/indent" "$dstpath/syntax"
cp -T "$srcpath/indent/protocon.vim" "$dstpath/indent/protocon.vim"
cp -T "$srcpath/syntax/protocon.vim" "$dstpath/syntax/protocon.vim"
if ! grep -q -e 'protocon' "$dstpath/filetype.vim"
then
  printf '%s' 'au BufRead,BufNewFile *.prot setfiletype protocon' >> "$dstpath/filetype.vim"
fi

