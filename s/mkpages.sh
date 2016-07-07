#!/bin/sh

git checkout gh-pages
git pull --no-edit origin master
make -C doc pub
rsync \
  --exclude=/examplespec/ \
  --exclude=/examplesett/ \
  --exclude=/examplesynt/ \
  --exclude=/examplesoln/ \
  -a doc/pubhtml/ ./
git status
echo 'Now commit, push, and change back to master.'

