
# Documentation

If the dependencies (below) are met, you can type `make` in this directory to create a local version of the documentation in `html/` or type `make pub` to create a standalone version in `pubhtml/`.
The only difference between these two versions is that `pubhtml/` also contains copies of the example spec files, so use that for putting the updating the actual website:

```
make pub
rsync -a pubhtml/ /path/to/www_asd/html/projects/protocon/
```


## Dependencies:

* man2html
  * This is standard on many Linux systems. It is part of the `sys-apps/man` package on Gentoo.
* tex2web
  * This should be built automatically in `../dep/`.
  * https://github.com/grencez/tex2web.git

