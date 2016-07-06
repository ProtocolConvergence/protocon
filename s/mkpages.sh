#!/bin/sh

git checkout gh-pages
git pull origin master
make -C doc pub
rsync \
  --exclude=/examplespec/ \
  --exclude=/examplesett/ \
  --exclude=/examplesynt/ \
  --exclude=/examplesoln/ \
  -a doc/pubhtml/ ./
git status
echo 'Now commit and change back to master.'

