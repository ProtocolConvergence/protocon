
proj_path=$(dirname $(dirname "${this_exe_path}"))
gen_exe="${proj_path}/bld/uni/generate"

function calc_domsz()
{
  local domsz btsz
  domsz=2
  btsz=$(printf '%s' "$1" | wc -c)
  while [ $(($domsz * $domsz * $domsz)) -lt $btsz ]
  do
    domsz=$(($domsz + 1))
  done
  printf '%s' $domsz
}

