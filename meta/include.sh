
init_distpath()
{
  distpath=$1

  if [ ! "$distpath" ]
  then
    distpath="$2"
  fi

  distpath=$(readlink -f "$distpath")
  distpath="$distpath-$(date '+%Y%m%d')"
}

make_doc()
{
  if ! make -C $1/doc
  then
    echo 'Cannot create documentation.' >&2
    exit 1
  fi
}

copy_examples()
{
  for d in examplespec examplesynt examplesoln
  do
    mkdir -p "$distpath/$d"
    cat "$metapath/$d.files" | \
    {
      while read f
      do
        cp -a -t "$distpath/$d" "$srcpath/$d/$f.prot"
      done
    }

    {
      echo "--- omitting the following files from $d/:"
      ls "$srcpath/$d" | sed -e 's/\.prot$//' | diff - "$metapath/$d.files"
    }>&2
  done
}

zip_up()
{
  cd "$(dirname "$distpath")"
  distname=$(basename "$distpath")
  #tar czf "$distname.tar.gz" "$distname"
  #chmod a+r,a-x "$distname.tar.gz"
  zip -r -q "$distname.zip" "$distname"
  chmod a+r,a-x "$distname.zip"
}

