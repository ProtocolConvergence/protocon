#!/bin/sh

old_name=$1
new_name=$2
for f in `ls "$new_name"`
do
  sort "$old_name/$f" > "tmp/$old_name$f"
  sort "$new_name/$f" > "tmp/$new_name$f"
  if ! diff -q "tmp/$old_name$f" "tmp/$new_name$f" >/dev/null
  then
    echo "$f"
  fi
  rm -f "tmp/$old_name$f" "tmp/$new_name$f"
done \
> "${old_name}-${new_name}.diffs"

