
# Coloring

## 3-Coloring on a Ring {#sec:ColorRing}

**ColorRing.**
([spec](../examplespec/ColorRing.prot),
[args](../examplesett/ColorRing.args),
([synt](../examplespec/ColorRing.prot),
[soln](../examplesoln/ColorRing.prot))

The `examplespec/ColorRing.prot` file specifies a bidirectional ring topology where each process wishes to obtain a different value than its neighbors.
Each process has 3 colors to choose from.
This is a very simple protocol and is useful for instruction.

See: [examplespec/ColorRing.prot](../examplespec/ColorRing.prot)

The invariant can also be specified outside of the process definition as:
```
(future & silent)
  (forall i <- Nat % N : c[i] != c[i+1]);
```
outside of the process definition.

The commands in this tutorial should be executed from within the top-level project directory on a Linux system.
First make a directory `tmp/` to store some files.
```
mkdir tmp
```

### Synthesis
Synthesize a 3-coloring protocol that works on rings of size 3, 4, and 5.
```
./bin/protocon -x examplespec/ColorRing.prot -param N 3..5 -o tmp/color.prot
```

### Verification
Check if the protocol is self-stabilizing rings of size 7. It should be fine!
```
./bin/protocon -verify -x tmp/color.prot -param N 7
```

### Model Checking with Spin
We can also verify this protocol's correctness in the [Spin model checker](http://spinroot.com) (here's a [quick setup guide](../../tut/spin.html)).
First output a model in the Promela language for a ring of 6 processes.
```
./bin/protocon -nop -x tmp/color.prot -param N 6 -o-promela tmp/color.pml
```
Now open the model in iSpin.
```
cd tmp
ispin color.pml
```
In the `Edit/View` tab, add the following lines to the end of the file.
This defines a predicate `Legit` that evaluates to true in all legitimate states.
There are also two temporal properties that define closure and convergence.
Closure ensures that once the ring has a valid coloring, no process will change its state in a way that violates that property.
Convergence ensures that from any initial state, the ring will eventually reach a valid coloring.
```
#define Legit
  (c[0] != c[1] && c[1] != c[2] &&
   c[2] != c[3] && c[3] != c[4] &&
   c[4] != c[5] && c[5] != c[0])
ltl Closure { [] (Legit -> [] Legit) }
ltl Convergence { [] <> Legit }
```
Perform a `Syntax Check`; there should be nothing to report.
Now switch to the `Verification` tab so we can verify that closure and convergence hold.
Under `Liveness`, ensure that the `acceptance cycles` bubble is filled.
Next, under `Never Claims`, click `use claim` and type `Closure` for the `claim name`.
Verify closure holds by clicking `Run`.
Now verify that covergence holds.
*Can you make a change to the 3-coloring protocol that breaks closure? How about convergence?*

### Parallel Search
When a problem instance is difficult, it may help to perform multiple searches at the same time using the `-parallel` flag.
Since multiple searches are occurring simultaneously, the search progress output is hidden.
This is remedied with the `-o-log` flag to create log files `search.log.``tid` for each thread of index `tid`.
```
./bin/protocon -parallel -x examplespec/ColorRing.prot -param N 3..5 -o tmp/color.prot -o-log tmp/color.log
```
If these log files are not desired, simply do not give the flag.

To control the number of threads used at runtime, simply give a number after the `-parallel` flag.
For example, imagine we want to use exactly 2 threads.

```
./bin/protocon -parallel 2 -x examplespec/ColorRing.prot -param N 5
```

## Distributed 3-Coloring on a Ring {#sec:ColorRingDistrib}

**ColorRingDistrib.**
([spec](../examplespec/ColorRingDistrib.prot),
[args](../examplesett/ColorRingDistrib.args),
[soln](../examplesoln/ColorRingDistrib.prot))

## Distance-2 5-Coloring on a Ring {#sec:ColorRingLocal}

**ColorRingLocal.**
([spec](../examplespec/ColorRingLocal.prot),
[args](../examplesett/ColorRingLocal.args),
[soln](../examplesoln/ColorRingLocal.prot))
