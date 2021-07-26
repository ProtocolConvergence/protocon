
## Release Notes

### 2016.10.20
* Benchmarks and updates to documentation
### 2016.07.05
* Prefer new syntax over `Nat % N` syntax
### 2015.09.29
* Add dining cryptographers, dining philosophers, and stop-and-wait examples
* Allow actions that are not self-disabling when a self-disabling version violates safety
* Make synthesis feasible for synchronous systems
* Fix crash when optimizing using MPI
* Fix `-=>` operator when used with random write variables, and change it to automatically randomize unassigned ones
* Fix `-=>` operator to not affect the guard for pure shadow variables
* New `random read:` access to variables for probabilistic stabilization
* New `(future & closed)` keyword for stabilization without enforcing a specific protocol behavior
### 2015.04.23
* New `random write:` access to variables for probabilistic stabilization
* New `(future & future silent)` and `(future & future shadow)` keywords for convergence to any subset of the invariant
* Daisy chain orientation example
* Can implicitly remove self-loops by using `-=>` in place of `-->`
* New `min(a,b)` and `max(a,b)` functions
### 2015.01.16
* Introduce `active shadow` which can be substituted for `shadow` to prevent shadow self-loops
* Change `permit:` semantics to make more intuitive sense
* More examples and documentation
### 2014.12.21
* New support for `shadow` variables
* Use .prot file extension
* MPI version now supports protocol optimization via the `-optimize` flag
* When using puppet variables, enforce a silent protocol with `future silent;` line
### 2014.09.12
* New `permit:` keyword to complement `forbid:`
* New `(assume & closed)` keyword to restrict initial states
* New `-optimize` flag for finding an optimal protocol (in interleaved steps)
* New `(future & silent)` or `(future & shadow)` syntax for invariants (see examples)
* Putting a `-def` before (but not after) `-x` in the argument list affects the initial file read and candidate actions
* More examples!
* Substantially more quality control and testing, associated bug fixes
### 2014.05.24
* File reorganization
* Preserve locally-conjunctive invariants
### 2014.04.26
* Serial search is now the default mode
* Improved packaging
* Improved file reading, still much room to improve
* Verification in GUI
### 2014.01.31
* Symmetry can be enforced across sets of variables.
* GUI gets a state exploration mode.
* Can now mark actions as forbidden. Synthesis cannot use them for recovery.
* Improve Promela model output.
* More testing and bug fixes.
### 2013.11.19
* Fix output format when multiple variables are used.
* Add ring orientation example

