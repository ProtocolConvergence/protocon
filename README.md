[https://github.com/ProtocolConvergence/protocon](https://github.com/ProtocolConvergence/protocon)\
[![Coverage Status](https://coveralls.io/repos/github/ProtocolConvergence/protocon/badge.svg?branch=trunk)](https://coveralls.io/github/ProtocolConvergence/protocon?branch=trunk)

# Protocon: Add Convergence to Shared Memory Protocols

Designing stabilizing protocols is hard, therefore Protocon exists to automate this task.
It performs a backtracking search to choose actions that finite-state processes should follow in order to converge to a set of legitimate states.
We call this [shadow/puppet synthesis](doc/legit.md), where the legitimate states and behavior can be specified indirectly using shadow variables.
Because the problem is hard, one can leverage multiple cores/nodes for parallel search with OpenMP (via the `-parallel` flag) or MPI (via the `protocon-mpi` executable).

## Resources
* `-->` [Tutorial](doc/tut.md) `<--`
* [Example Protocols](example/index.md)
* [Benchmarks](doc/benchmark.md)
* [Different ways to specify legitimate states and behavior](doc/legit.md)
* [Action constraints and syntax](doc/permit.md)
* [Man Page](doc/protocon.1)
* [Release Notes](doc/changes.md)
* [Acknowledgements](doc/thanks.md)

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
git clone https://github.com/ProtocolConvergence/protocon.git protocon
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

* peg - http://piumarta.com/software/peg/ and [mirrored on GitHub](https://github.com/gpakosz/peg/)
  * Parser.
* glu 2.4 - [forked on GitHub](https://github.com/ProtocolConvergence/mdd-glu)
  * Library for multi-valued decision diagrams (MDDs).
* Qt5 (optional)
  * For the gui.
* espresso (optional)
  * http://code.google.com/p/eqntott/downloads/detail?name=espresso-ab-1.0.tar.gz
  * Logic minimization tool when -espresso flag is used.

## Thanks

* This work was sponsored by the NSF grant CCF-1116546.
* **Superior**, a high performance computing cluster at Michigan Technological University, was used in obtaining benchmarks and some results.

