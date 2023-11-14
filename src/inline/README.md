# Inline Function Library

When deciding how to write repetative code snippets, your first thought should be to functionalize it.
I usually start with a file-local function.
If it has to be used across multiple files, then put the function alongside others that operate on similar data types.

But what if there's no appropriate header file?
That's where an inline function library shines.
We write the file-local function in a header file and leverage `#include` as a copy-paste.
This is a way to manage scope even without a perfect solution.

