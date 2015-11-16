" Vim indent file
" Language:     Protocon
" Author:       Alex Klinkhamer (grencez@*)
" URL:          http://github.com/grencez/protocon/


" Only load this indent file when no other was loaded.
if exists("b:did_indent")
  finish
endif
let b:did_indent = 1

setlocal indentexpr=GetProtoconIndent()
setlocal indentkeys=0{,0},0),0],!^F,o,O,e
setlocal indentkeys+=od,fi,then,->,/,:,;

" Only define the function once.
if exists("*GetProtoconIndent")
  finish
endif

let s:blockbeg = '^\s*\(.*{\)\s*$'
let s:blockend = '^\s*}\s*$'
let s:guard = '^\s*::.*$'

function GetProtoconIndent()

  " Get current line
  let line = getline(v:lnum)
  if line =~ '^\s*$'
    "return 0
  endif

  if v:lnum == 0
    return 0
  endif

  let pnum = prevnonblank(v:lnum - 1)
  let pline = getline(pnum)

  if pnum == 0
    return 0
  endif

  let bnum = pnum
  let bline = pline

  let parencol = 0
  let nparens = 0

  if line =~ '^\s*).*$'
    let parencol = -1
  endif

  let linecont = -1

  while bnum > 0 && (linecont == -1 || nparens > 0 || parencol < 0 || bline =~ '^\s*//.*$' || !(bline =~ '^\(.*;\|\s*{\|\s*}\)\s*$'))

    " Ignore comment.
    if bline =~ '^\s*//.*$'
      let bline = ''
    else
      let pnum = bnum
      let pline = bline
      if linecont == -1
        if bline =~ '^\(.*;\|\s*{\|\s*}\)\s*$'
          let linecont = 0
        else
          let linecont = 1
        endif
      endif
    endif

    let col = strlen(bline)
    for c in reverse(split(bline, '\zs'))
      if c == '('
        if nparens == 0
          let parencol = col
          break
        endif
        let nparens = nparens - 1
      elseif c == ')'
        let nparens = nparens + 1
      endif
      let col = col - 1
    endfor
    unlet col
    if parencol > 0
      break
    endif

    if bline =~ s:blockbeg || bline =~ s:blockend
      break
    endif

    let bnum = prevnonblank(bnum - 1)
    let bline = getline(bnum)
  endwhile
  unlet nparens

  if parencol > 0
    if line =~ '^\s*).*$'
      return parencol - 1
    endif
    return parencol
  endif

  let ind = indent(pnum)

  if line =~ s:blockbeg
    " Nothing
  elseif line =~ s:blockend
    let ind = ind - &sw
    if ind < 0
      let ind = 0
    endif
  elseif linecont == 1 || pline =~ s:blockbeg
    let ind = ind + &sw
  endif

  return ind
endfunction

function s:PrevMatchBlock(end)
  if a:end == '}'
    let begin = '{'
    let end = '}'
  else
    let begin = '\<if\>'
    let end = '\<else\>'
  endif

  call search(end, 'bW')
  return searchpair(begin, '', end, 'Wbn')
endfunction

