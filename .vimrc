
set tabstop=2
set shiftwidth=2
set expandtab
set cinoptions=(0

""" Put this at the top of your .vimrc:
" set nocompatible "< No vi bugs
" if exists("g:vimrcsourced")
"     finish
" endif
" let g:vimrcsourced = 1

""" Put this at the bottom of your .vimrc:
" " Get project-specific .vimrc mods!
" let dir = getcwd()
" let extra_vimrc = dir . '/.vimrc'
" while ! filereadable(extra_vimrc) && dir != ''
"     let dir = substitute(dir, '/[^/]*$', '', '')
"     let extra_vimrc = dir . '/.vimrc'
" endwhile
" 
" if filereadable(extra_vimrc)
"     execute "source " . extra_vimrc
" endif

