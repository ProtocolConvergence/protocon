
# Tutorial

Welcome to the Protocon tutorial!
If you haven't already, please download the latest Linux binary from [the main page](https://github.com/grencez/protocon).
Next, open up a terminal, navigate to the download location, unzip it, and enter the resulting directory.
```
cd ~/Downloads
unzip protocon-bin-YYYYMMDD.zip
cd protocon-bin-YYYYMMDD
```
Where `YYYYMMDD` is the current version number.

**Tip:** You can copy and paste commands by highlighting the text and middle-clicking in a terminal.
(Though it's not always the best thing to do [security-wise](http://thejh.net/misc/website-terminal-copy-paste)).


## Coloring

The file [examplespec/ColorRing.prot](../examplespec/ColorRing.prot) specifies a bidirectional ring topology where each process wishes to obtain a different value than its two neighbors.
Each process has 3 colors to choose from.
We can synthesize actions for this protocol by issuing the command:
```
./bin/protocon -x examplespec/ColorRing.prot -o tmp/color.prot
```
And we can verify that the resulting protocol is stabilizing:
```
./bin/protocon -verify -x tmp/color.prot
```

Remove the file
```
rm tmp/color.prot
```
and open the original specification in a GUI.
```
./bin/protocon-gui examplespec/ColorRing.prot
```

The GUI allows us to perform synthesis and verification in the same way.
First, change the output file name to `tmp/color.prot`.
Next, push the `Synthesize` button.
After success, close the pop-up window and open the resulting protocol file by pushing the `Open` button below the output file name or using the `File` menu.
With the protocol file opened, verify it by pushing the `Verify` button.

The GUI also lets us manually walk through a protocol's execution.
To do this, push the `Explore` button.
This new window shows the system's current state (i.e., `Values` of all variables), all possible states reached by a single process acting (i.e., `Forward` transitions), and all possible previous states (i.e., `Backward` transitions).
The initial state has all `x` values set to 0, which can be changed by selecting a variable and typing a number.
Alternatively, the `Randomize State` button will randomize all values.

The exploration window also shows if the current state is within the specified invariant (all neighboring processes have different colors), is silent (no process will act), or is part of a cycle (can be reached infinitely often).
Cycle detection can be time consuming for large systems, therefore one must push the `Find Cycles` button for cycle information.
We can also `Restrict` our view to a combination of these these predicates.
Try clicking the `false` radio button for the `invariant` predicate and then press the `Randomize State` button.
We are brought to a state where some process shares the same color as its neighbor.
The forward and backward transitions are also restricted.
To see this, click one of the `Forward` transitions or the `Step Forward` button a few times until the state no longer changes.
The system has not yet formed a valid coloring!
Clicking the `or` or `true` radio button for the `invariant` predicate reveals a final transition (or two) to reach the invariant.


## Maximal Matching

The file [examplespec/MatchRingThreeState.prot](../examplespec/MatchRingThreeState.prot) specifies a bidirectional ring topology where each process wishes to match with one of its neighbors.
When `x[i]` is 0 or 2, process `P[i]` is pointing to `P[i-1]` or `P[i+1]` respectively.
Two processes are matched together when they point to each other.
Sometimes a perfect matching is impossible, so any process `P[i]` can remain unmatched (with `x[i]` equaling 1) when both of its neighboring processes are matched.

We can synthesize actions for this protocol on a ring of size 4 by issuing the command:
```
./bin/protocon -x examplespec/MatchRingThreeState.prot -o tmp/match.prot -def N 4
```

**Note:** To avoid mistakes, prefer to place the `-def` flag after the `-x` flag.
When the definition will affect variable domains, prefer to edit the file directly or place `-def` before `-x`.
(Protocon will catch these problems and advise you.)

Does the resulting protocol stabilize on ring of size 3?
```
./bin/protocon -verify -x tmp/match.prot -def N 3
```
Probably not. Let's investigate the issue.

Open the file in a GUI.
```
./bin/protocon-gui tmp/match.prot
```
Change the constant `N` to 3 by modifying the text to have `constant N := 3;` on the first line.

To investigate the deadlock, click `Explore` and select `false` for the `invariant` predicate and `true` for the `silent` predicate.
Click the `Randomize State` button to find a deadlock state.
Close the GUI.

To fix this, we must synthesize a protocol that stabilizes for rings of multiple sizes.
Let's do this for rings of size 3, 4, and 5.
```
./bin/protocon -x examplespec/MatchRingThreeState.prot -o tmp/match.prot -def N 3 -param N 4 -param N 5
```
%Note: Using the `-param` flag when it affects variable domains will result in an error.


## Sum-Not-2

The file [examplespec/SumNotTwo.prot](../examplespec/SumNotTwo.prot) specifies a unidirectional ring topology where we do not want the sum of any two consecutive values to equal 2.
Open the file in the GUI and add the following three actions at the end of the process block:
```
  puppet action:
    ( x[i-1]==0 && x[i]==2 --> x[i]:=0; )
    ( x[i-1]==1 && x[i]==1 --> x[i]:=2; )
    ( x[i-1]==2 && x[i]==0 --> x[i]:=2; )
    ;
```

Try the following:
1. Use the exploration window to find a livelock (a cycle outside of the invariant).
1. What is happening in the livelock?
1. How can the last action be modified in order to remove the livelock?
   * Hint: Remove the last action and run synthesis.


## Sum-Not-Odd

Consider a sum-not-odd protocol on a unidirectional ring that stabilizes to states where the sum of any two consecutive numbers is even.
We will see how Protocon can optimize performance and also help with manual construction of a protocol.

Try the following:
1. Specify the sum-not-odd problem using [examplespec/SumNotTwo.prot](../examplespec/SumNotTwo.prot) as a template.
   * Use the mod operator `%`.
   * Keep variable domains at size `M=3`.
1. Synthesize a sum-not-odd protocol that stabilizes on rings of size 2, 3, 4, and 5.
1. Verify that it stabilizes on a ring of size 8.
   * Note the number reported after `Max async layers to fixpoint:`, this is the worst-case number of steps to converge on a ring of size 8.
1. Synthesize a sum-not-odd protocol again for `N=2,3,4,5`, and add the `-optimize` flag to the command.
1. Verify that the resulting protocol stabilizes on a ring of size 8.
   * Note that the worst-case number of convergence steps is smaller than before.

We would now like to create a general sum-not-odd protocol for any variable domain of size `M`.
One problem is that randomization is used during synthesis, which gives a random-looking protocol.
1. Synthesize a sum-not-odd protocol again for `N=2,3,4,5`, and add the `-optimize` and `-no-random` flags to the command.
   * Save this result somewhere.
1. Change variable domains to `M=4` in the file.
1. Repeat step 1.
1. Change variable domains to `M=5` in the file.
1. Repeat step 1.
1. Looking at these protocols, can you devise a sum-not-odd protocol that stabilizes for any domain size `M`?


## Maximal Matching with Shadow/Puppet Synthesis

In graph theory, maximal matching is defined in terms of edges rather than nodes (i.e., processes).
We would like to do the same, but placing a variable between each process is unrealistic in a distributed system.

Using shadow puppetry as a metaphor, we can split the concept of desired behavior away from implementation.
We want to cast a particular shadow upon a screen by placing a well-crafted puppet between the screen and a light.
Instead of building the puppet ourselves, we can ask a clever puppeteer to build it for us.
In this metaphor, the clever puppeteer is Protocon, the shadow is our desired invariant and behavior, the puppet is the synthesized protocol.

The [examplespec/MatchRing.prot](../examplespec/MatchRing.prot) file uses this technique to specify matching on edge variables where:

* No two adjacent edges can be selected.
* At least one of every three consecutive edges must be selected.

Edge variables are declared with the `shadow` keyword since they will not exist in the implementation, therefore their values must be derived from the `puppet` variables.
Generally, the invariant and behavior constraints should only apply for some values of puppet variables, so these constraints are specified as `((future & silent) % puppet)` rather than the usual `(future & silent)`.

The [examplesynt/MatchRing.prot](../examplesynt/MatchRing.prot) contains a synthesized protocol for this system.
Notice that the `e` values are fully derived from `x` values.
Therefore, the protocol can be implemented without `e` values at all!
See [examplesoln/MatchRingOneBit.prot](../examplesoln/MatchRingOneBit.prot) for this transformation.


## Next Steps

This concludes the tutorial.
To see what else is possible (beyond silent protocols on rings), browse our ever-growing list of example protocols.
For a complete feature list (such as the `-parallel` or `-x-args` options), browse the manual page.

* [example/index.md](example/index.md) - List of example files.
* [legit.md](legit.md) - More ways to specify the invariant and behavior.
* [man.md](man.md) - Manual page.

Email the author@mtu.edu, where the author is apklinkh, with questions/bugs/requests.
