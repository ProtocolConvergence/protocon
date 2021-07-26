
# Protocol Examples

Example files are given in three directories: (1) [examplespec](../examplespec) contains problem specifications, (2) [examplesoln](../examplesoln) contains solutions, and (3) [examplesynt](../examplesynt) contains solutions that retain artifacts from the specification.
For each file in [examplesynt](../examplesynt), there is usually a corresponding file in [examplesoln](../examplesoln) that is more presentable and simpler to verify.

## Sum-Not-2

Aly Farahat's [dissertation](http://digitalcommons.mtu.edu/etds/178) includes a simple yet nontrivial unidirectional ring protocol.
It has been extremely helpful for reasoning about the nature of [livelocks in unidirectional rings](http://dx.doi.org/10.1007/978-3-319-03089-0\_12) and has a simple enough transition system to actually show in a presentation.

* SumNotTwo ([spec](../examplespec/SumNotTwo.prot))
* SumNotTarget ([spec](../examplespec/SumNotTarget.prot), [soln](../examplesoln/SumNotTarget.prot)) -
  The general case sum-not-(l-1) protocol given by Farahat.

## Coloring

[Graph coloring](http://en.wikipedia.org/wiki/Graph_coloring) is a well-known problem with many applications.
Each node in the graph is assigned a color.
For this assignment to be called a \textit{coloring}, each node must have a different color than the nodes adjacent to it.
In a computer network, a coloring applies to processes that communicate directly with each other rather than nodes connected by edges.

* ColorRing [info](Coloring.md#sec:ColorRing) -
  3-coloring on a ring.
* ColorRingDizzy ([spec](../examplespec/ColorRingDizzy.prot), [soln](../examplesoln/ColorRingDizzy.prot)) -
  Unoriented ring.
* ColorUniRing ([spec](../examplespec/ColorUniRing.prot), [soln](../examplesoln/ColorUniRing.prot)) -
  Randomized 3-coloring on a unidirectional ring.
* ColorRingLocal [info](Coloring.md#sec:ColorRingLocal) -
  Randomized distance-2 coloring on a unidirectional ring using 5 colors.
  Neither a process or its neighbors can have the same color as another neighbor.
* ColorRingDistrib [info](Coloring.md#sec:ColorRingDistrib) -
  Randomized 3-coloring on a ring where processes have communication delay.
* ColorChain ([spec](../examplespec/ColorChain.prot)) -
  2-coloring on a chain.
* ColorTree ([spec](../examplespec/ColorTree.prot), [soln](../examplesoln/ColorTree.prot)) -
  Tree.
* ColorTorus ([spec](../examplespec/ColorTorus.prot)) -
  Torus.
* ColorMobius ([spec](../examplespec/ColorMobius.prot)) -
  Mobius ladder.
* ColorKautz ([spec](../examplespec/ColorKautz.prot)) -
  4-coloring on generalized Kautz graph of degree 2.

We can find a protocol that stabilizes for up to 13 processes, but not 14.
Tweaking the topology by
[reversing edges](../examplespec/ColorKautzReverse.prot)
or
[removing orientation](../examplespec/ColorKautzDizzy.prot)
(even with [bidirectional edges](../examplespec/ColorKautzBi.prot))
gives definite impossibility results at around 8 processes.

## Maximal Matching

[Matching](http://en.wikipedia.org/wiki/Matching_(graph_theory)) is well-known problem from graph theory.
A matching is a set of edges that do not share any common vertices.
For a matching to be \textit{maximal}, it must be impossible to add another edge to the set without breaking the matching property.

* MatchRing [info](Matching.md#sec:MatchRing) -
  Natural specification for matching using the edges in the ring.
  This gives the 1-bit solution.
* MatchRingThreeState [info](Matching.md#sec:MatchRingThreeState) -
  Maximal matching on a ring where processes point in certain directions.
* MatchRingOneBit [info](Matching.md#sec:MatchRingOneBit) -
  Using the 3-state specification, find a matching using 1 bit per process.
* MatchRingDizzy ([spec](../examplespec/MatchRingDizzy.prot), [args](../examplesett/MatchRingDizzy.args)) -
  Maximal matching on an unoriented ring.
* SegmentRing [info](Matching.md#sec:SegmentRing) -
  A problem similar to matching where a ring is segmented into chains.

## Sorting on Chains and Rings

* SortChain ([spec](../examplespec/SortChain.prot), [soln](../examplesoln/SortChain.prot)) -
  Sorting a chain of values.
  Easy to synthesize, but solution is manually simplified.
* SortRing ([spec](../examplespec/SortRing.prot), [soln](../examplesoln/SortRing.prot)) -
  Sorting a ring of values using a unique zero value to mark the beginning of the sequence.
  Easy to synthesize, but solution is manually simplified.

## Orientation

* OrientDaisy [info](Orientation.md#sec:OrientDaisy) -
  Silent orientation for daisy chains (either ring and chain), verified for 2 to 15 processes.
  The version in [examplesoln](../examplesoln) behaves similarly, is simpler, but is slightly less optimal.
* OrientRing [info](Orientation.md#sec:OrientRing) -
  Manually designed silent ring orientation, verified for 2 to 26 processes.
  Also works under synchronous scheduler.
* OrientRingOdd [info](Orientation.md#sec:OrientRingOdd) -
  From [Hoepman](http://dx.doi.org/10.1007/BFb0020439).
* OrientRingViaToken ([spec](../examplespec/OrientRingViaToken.prot), [soln](../examplesoln/OrientRingViaToken.prot)) -
  From [Israeli and Jalfon](http://dx.doi.org/10.1006/inco.1993.1029).

## Token Passing

* TokenRingFiveState [info](TokenPassing.md#sec:TokenRingFiveState) -
  5-state token ring whose behavior is specified with shadow variables.
* TokenRingSixState [info](TokenPassing.md#sec:TokenRingSixState) -
  6-state token ring specified with variable superposition.
* TokenRingThreeBit [info](TokenPassing.md#sec:TokenRingThreeBit) -
  3-bit token ring from [Gouda and Haddix](http://dx.doi.org/10.1006/jpdc.1996.0066).
* TokenRingFourState ([synt](../examplesynt/TokenRingFourState.prot)) -
  4-state token ring specified with variable superposition.
  This version is only stabilizing for 2 to 7 processes.
  It operates much like the 3-bit token ring.
* TokenRingDijkstra [info](TokenPassing.md#sec:TokenRingDijkstra) -
  Dijkstra's stabilizing token ring.
* TokenChainThreeState [info](TokenPassing.md#sec:TokenChainThreeState) -
  3-state token passing on a chain topology.
* TokenChainDijkstra [info](TokenPassing.md#sec:TokenChainDijkstra) -
  Dijkstra's 4-state token passing on a chain topology.
* TokenRingThreeState [info](TokenPassing.md#sec:TokenRingThreeState) -
  3-state token passing on a bidirectional ring.
  One solution is from Dijkstra, the other is from [Chernoy, Shalom, and Zaks](http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.153.6017).
* TokenRingOdd ([spec](../examplespec/TokenRingOdd.prot), [soln](../examplesoln/TokenRingOdd.prot)) -
  Randomized token passing protocol on odd-sized rings.

<--- Leader Election -->
<--- Reduction from 3-SAT -->

## Other

* ByzantineGenerals ([spec](../examplespec/ByzantineGenerals.prot), [soln](../examplesoln/ByzantineGenerals.prot)) -
  The Byzantine generals problem formulated as an instance of self-stabilization.
* DiningCrypto ([spec](../examplespec/DiningCrypto.prot), [soln](../examplesoln/DiningCrypto.prot)) -
  The dining cryptographers problem as an instance of self-stabilization, where the initial state is assumed to randomize the coins.
  We can't model anonymity, only determination of whether a cryptographer or the NSA pays for dinner.
* DiningPhilo ([spec](../examplespec/DiningPhilo.prot), [soln](../examplesoln/DiningPhilo.prot)) -
  The dining philosophers problem. This version assumes a coloring in order to break symmetry.
* DiningPhiloRand ([spec](../examplespec/DiningPhiloRand.prot), [soln](../examplesoln/DiningPhiloRand.prot)) -
  The dining philosophers problem. This version uses randomization to break symmetry.
* LeaderRingHuang ([spec](../examplespec/LeaderRingHuang.prot), [soln](../examplesoln/LeaderRingHuang.prot)) -
  Leader election protocol on prime-sized rings from [Huang](http://dx.doi.org/10.1145/169683.174161).
* Sat ([spec](../examplespec/Sat.prot)) -
  Example reduction from 3-SAT to adding stabilization from our [paper showing NP-completeness](http://dx.doi.org/10.1007/978-3-642-40213-5_2) of adding convergence.
* StopAndWait ([spec](../examplespec/StopAndWait.prot), [soln](../examplesoln/StopAndWait.prot)) -
  The Stop-and-Wait protocol, otherwise known as the Alternating Bit protocol when the sequence number is binary.

