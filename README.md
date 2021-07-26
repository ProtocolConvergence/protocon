[![Coverage Status](https://coveralls.io/repos/github/grencez/protocon/badge.svg?branch=trunk)](https://coveralls.io/github/grencez/protocon?branch=trunk)

# Protocon

Designing stabilizing protocols is hard, therefore Protocon exists to automate this task.
It performs a backtracking search to choose actions that finite-state processes should follow in order to converge to a set of legitimate states.
We call this [shadow/puppet synthesis](legit.md), where the legitimate states and behavior can be specified indirectly using shadow variables.
Because the problem is hard, one can leverage multiple cores/nodes for parallel search with OpenMP (via the `-parallel` flag) or MPI (via the `protocon-mpi` executable).
The project's main page http://asd.cs.mtu.edu/projects/protocon/ contains executables and short tutorials.

## How to Run

Just type `make` from the top-level directory to build object files in `bld/` and place the main executables there.

```
make
mkdir tmp
./bld/protocon -x examplespec/ColorRing.prot -o tmp/solution.prot
```

### Full Instructions

```
# Get the code.
git clone https://github.com/grencez/protocon.git protocon
cd protocon

# Build with CMake.
mkdir -p bld
cd bld
cmake ..
cmake --build . --config Release
cd ..

# Synthesize 3-coloring protocol.
mkdir tmp
./bld/protocon -x examplespec/ColorRing.prot -o tmp/solution.prot
```

If you're on a Mac, read on.
Was CMake not found?
If so, make sure it's installed and launch its GUI.
Specify its source directory as `/path/to/protocon/src/` and the build directory as `/path/to/protocon/bld/`.
Hit the `Generate` button.

Now there should be a makefile in `bld/`, so in the terminal type `make`.

## Dependencies:

All essential dependencies are automatically downloaded during compilation.

* peg
  * http://piumarta.com/software/peg/
  * Parser.
* glu 2.4
  * ftp://vlsi.colorado.edu/pub/vis/
  * Library for multi-valued decision diagrams (MDDs).
* Qt5 (optional)
  * For the gui.
* espresso (optional)
  *  http://code.google.com/p/eqntott/downloads/detail?name=espresso-ab-1.0.tar.gz
  * Logic minimization tool when -espresso flag is used.

## Thanks

* This work was sponsored by the NSF grant CCF-1116546.
* **Superior**, a high performance computing cluster at Michigan Technological University, was used in obtaining benchmarks and some results.

