# Shell script

# Constants.
maxdepth=10000

# Maximum amount of memory.
# 2000000 = 2 GB
ulimit -v 2000000

eputs()
{
  echo "$@" >&2
}

pmlf=$1
if [ ! "$pmlf" ]
then
  eputs "Give a filename!"
  exit 1
fi

ltlname=$2
if [ "$mode" = "ltl" ]
then
  #if [ ! "$ltlname" ]
  #then
  #  ltlname=$(grep -m 1 -o -e '^ *ltl \+[^ {]\+' "$pmlf" | grep -o -e '[^ ]\+$')
  #fi
  #if [ ! "$ltlname" ]
  #then
  #  n=$(grep -e '^ *ltl[ {$]' "$pmlf" | wc -l)
  #  if [ "$n" -eq 0 ]
  #  then
  #    eputs "No LTL claim is defined. What are you doing?"
  #    exit 1
  #  elif [ "$n" -gt 1 ]
  #  then
  #    eputs "More than 1 LTL claim is defined. Please name them!"
  #    exit 1
  #  fi
  #fi

  if [ "$ltlname" ]
  then
    eputs "Using LTL claim: $ltlname"
  else
    eputs "Using the only LTL claim."
  fi
fi

tmpf="${pmlf}.tmp"


cleanup()
{
  rm -f pan* "$tmpf"
}

generate_pan()
{
  args="-a"
  spin $args "$pmlf" >"$tmpf" 2>&1
  ret=$?
  #grep -v '^ltl ' "$tmpf" >&2
  if [ "$ret" != 0 ]
  then
    cat "$tmpf" >&2
    eputs "Failed to generate pan.c"
    exit 1
  fi

  if [ "$mode" = "ltl" ]
  then
    if ! grep -q -e "^ltl $ltlname" "$tmpf"
    then
      if [ ! "$ltlname" ]
      then
        eputs "No LTL claim is defined. What are you doing?"
      else
        eputs "No LTL claim named '$ltlname' is defined."
      fi
      exit 1
    fi
  fi
}

compile_pan()
{
  args="-DXUSAFE"
  if [ "$mode" = "safe" ]
  then
    args="$args -DSAFETY -DNOCLAIM"
  elif [ "$mode" = "live" ]
  then
    args="$args -DNP -DNOCLAIM"
  fi

  args="$args -O2"

  gcc $args pan.c -o pan >"$tmpf" 2>&1
  ret=$?
  if grep -q -e "NOREDUCE" "$tmpf"
  then
    args="$args -DNOREDUCE"
    gcc $args pan.c -o pan >"$tmpf" 2>&1
    ret=$?
  fi

  cat "$tmpf" >&2
  if [ "$ret" != 0 ]
  then
    eputs "Failed to compile pan.c"
    exit 1
  fi
}

run_pan()
{
  args="-b -m${maxdepth}"
  if [ "$mode" = "live" ]
  then
    args="$args -l"
  elif [ "$mode" = "ltl" ]
  then
    args="$args -a"
    if [ "$ltlname" ]
    then
      args="$args -N $ltlname"
    fi
  fi

  ./pan $args 2>&1 \
  | grep -v --line-buffered \
    -e "_nvr" \
    -e "unreached in claim" \
    -e "([^ ]* of [^ ]* states)" \
  | tee "$tmpf"

  ret=1

  if grep -q -e 'errors: 0' "$tmpf"
  then
    ret=0
  fi

  if grep -q -e 'pan: *out *of *memory' "$tmpf"
  then
    ret=1
  fi

  eputs ""
  if [ "$ret" = 0 ]
  then
    eputs "SUCCESS"
    if [ "$mode" = "live" ]
    then
      eputs "No livelocks found. Be sure to check safety!"
    elif [ "$mode" = "safe" ]
    then
      eputs "No safety violations. Be sure to check for livelocks!"
    else
      eputs "No counterexamples found."
    fi
  else
    eputs "FAILURE"

    if grep -q -e 'non-progress cycle (at depth' "$tmpf"
    then
      eputs "Livelock found."
    fi

    if grep -q -e 'invalid end state (at depth' "$tmpf"
    then
      eputs "Deadlock found."
    fi

    if grep -q -e 'pan: *out *of *memory' "$tmpf"
    then
      eputs "Out of memory."
    fi

    if grep -q -e 'error: max search depth too small' "$tmpf"
    then
      eputs "Max search depth was too small. You can increase it in $spinclude"
      if [ "$mode" = "safe" ]
      then
        eputs "But first, try checking for livelocks!"
      fi
    elif grep -q -e "wrote ${pmlf}.trail" "$tmpf"
    then
      eputs "Counterexample written to: ${pmlf}.trail"
      eputs "Replay N steps: spinplay ${pmlf} N"
      eputs "Replay all steps: spinplay ${pmlf}"
    fi
  fi
  return $ret
}

