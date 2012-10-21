#!/bin/sh

###### README ######
# The environment variables:
# GDIFF and EDITOR can override what command is used to display
# a diff or view a newly added file (respectively).
# I suggest installing 'xxdiff', which is used by default.
# For the viewing new files, 'less' is used by default.
#
# To use gvim, put:
#   export GDIFF='gvim -fd'
#   export EDITOR='gvim -f'
# in your ~/.bashrc file.
######

if [ $# -eq 0 ]
then
  set -- .
fi

if [ -z "$GDIFF" ]
then
  GDIFF='xxdiff'
fi

if [ -z "$EDITOR" ]
then
  EDITOR='less'
fi

vcs=svn
if ls -a | grep -q '^\.git$'
then
    vcs=git
fi

newfiles_svn()
{
    svn stat -q "$1" | \
    awk -- '$1 == "A" { print $NF; }'
}

modfiles_svn()
{
    svn stat -q "$1" | \
    awk -- '$1 == "M" { print $NF; }'
}

catfile_svn()
{
    svn cat "$1" > "$2"
}

newfiles_git()
{
    git status -s "$1" | \
    awk -- '$1 == "A" { print $NF; }'
}

modfiles_git()
{
    git status -s "$1" | \
    awk -- '$1 == "M" { print $NF; }'
}

catfile_git()
{
    git show HEAD:"$1" > "$2"
}

newfiles()
{
    # Show new files.
    case "$vcs" in
        svn) newfiles_svn "$@" ;;
        git) newfiles_git "$@" ;;
    esac
}

modfiles()
{
    # Show modified files.
    case "$vcs" in
        svn) modfiles_svn "$@" ;;
        git) modfiles_git "$@" ;;
    esac
}

catfile()
{
    case "$vcs" in
        svn) catfile_svn "$@" ;;
        git) catfile_git "$@" ;;
    esac
}

# Redirect stdin to file descriptor 3,
# required for vim to not screw up the console.
exec 3<&0

while [ $# -gt 0 ]
do
  file="$1"
  shift

  { newfiles "$file" ; } | \
  # Show newly added files.
  while read -r f
  do
    printf 'ADD %s\n' "$f"
    # Don't show directories.
    if [ ! -d "$f" ]
    then
      $EDITOR "$f" <&3
    fi
  done

  { modfiles "$file" ; } | \
  while read -r f
  do
    tmpf=`mktemp`
    printf 'MOD %s\n' "$f"
    catfile "$f" "$tmpf"
    $GDIFF "$tmpf" "$f" <&3
    rm "$tmpf"
  done
done

