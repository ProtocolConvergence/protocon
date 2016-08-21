
proj_path=$(dirname $(dirname "${this_exe_path}"))
gen_exe="${proj_path}/bld/uni/generate"

function calc_domsz()
{
  local domsz btsz
  domsz=2
  btsz=$(printf '%s' "$1" | wc -c)
  while expr $domsz '*' $domsz '*' $domsz '<' $btsz >/dev/null
  do
    domsz=$(expr $domsz '+' 1)
  done
  printf '%s' $domsz
}

