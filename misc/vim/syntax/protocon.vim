" Vim syntax file
" Language:	Protocon
" Maintainer:	Alex Klinkhamer <grencez@*>
" Last Change:	2015 Oct 27
" Filenames:	*.prot
" URL:		http://github.com/grencez/protocon/
" Credits: 	Some ideas has been stolen from the official c.vim file.

" Quit when a (custom) syntax file was already loaded
if exists("b:current_syntax")
	finish
endif

syntax case match

" Comments
syn region	protoconComment		start="//" skip="\\$" end="$" keepend

" Identifiers
syn keyword	protoconFunction		min max
syn keyword	protoconFunction		map
syn keyword	protoconType		Nat Int
syn match	protoconNumber		"\<[0-9]\+\>"
syn keyword	protoconLiteral		 true false

syn keyword	protoconConditional	if then else --> -=>

" Statements
syn keyword 	protoconStatement  constant variable predicate process let read write
syn keyword 	protoconStatement  action permit forbid conflict random symmetric
syn keyword 	protoconQual	shadow puppet direct
syn keyword 	protoconQual    future assume closed silent active
syn keyword 	protoconQuant   forall exists unique

" Define the default highlighting.
hi def link protoconComment		Comment
hi def link protoconFunction		Function
hi def link protoconNumber		Number
hi def link protoconLiteral		Number
hi def link protoconType		Type
hi def link protoconQual	Define
hi def link protoconQuant	Function
hi def link protoconStatement		Define
hi def link protoconConditional		Conditional

let b:current_syntax = "protocon"

" vim: ts=8
