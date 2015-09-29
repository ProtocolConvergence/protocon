
# Protocon

Designing stabilizing protocols is hard, therefore Protocon exists to automate this task.
It performs a backtracking search to choose actions that finite-state processes should follow in order to converge to a set of legitimate states.
We call this [shadow/puppet synthesis](http://asd.cs.mtu.edu/projects/protocon/legit.html), where the legitimate states and behavior can be specified indirectly using shadow variables.
Because the problem is hard, one can leverage multiple cores/nodes for parallel search with OpenMP (via the `-parallel` flag) or MPI (via the `protocon-mpi` executable).
The project's main page http://asd.cs.mtu.edu/projects/protocon/ contains executables and short tutorials.

## How to Run

Just type `make` from the top-level directory to build object files in `bld/` and place the resulting executables in `bin/`.

```
make
mkdir tmp
./bin/protocon -x examplespec/ColorRing.prot -o tmp/solution.prot
```

## Dependencies:

Besides Qt, all essential dependencies are automatically downloaded when running `make`.

* peg >=0.1.11
  * http://piumarta.com/software/peg/
  * Parser.
* glu 2.4
  * ftp://vlsi.colorado.edu/pub/vis/
  * Library for multi-valued decision diagrams (MDDs).
* Qt4 4.8
  * For the gui.
* espresso
  *  http://code.google.com/p/eqntott/downloads/detail?name=espresso-ab-1.0.tar.gz
  * Optional logic minimization tool when -espresso flag is used.

## Thanks

* This work is sponsored by the NSF grant CCF-1116546.
* **Superior**, a high performance computing cluster at Michigan Technological University, was used in obtaining benchmarks and some results.

