
# One-Bit Maximal Matching on a Ring

[Matching](http://en.wikipedia.org/wiki/Matching_(graph_theory)) is well-known problem from graph theory.
A matching is a set of edges that do not share any common vertices.
For a matching to be *maximal*, it must be impossible to add another edge to the set without breaking the matching property.

## 1-Bit Maximal Matching on a Ring {#sec:MatchRing}

**MatchRing.**
([spec](../examplespec/MatchRing.prot),
 [args](../examplesett/MatchRing.args),
 [synt](../examplesynt/MatchRing.prot)
 [soln](../examplesoln/MatchRingOneBit.prot))

In the specification, the `e` variables denote whether an edge is in the matching.
The invariant specified as a maximal matching, which can be restated as the following two conditions for the special case of a ring:

* No two adjacent edges can be selected.
* At least one of every three consecutive edges must be selected.

**Synthesis.**
Processes cannot realistically write to edge variables, therefore the `e` variables are marked as `shadow` and their values must be derived from `x` values owned by processes.
For an instructive look at how this works see [the next section](#sec:MatchRingOneBit), which derives the same protocol from a slightly different way of specifying the maximal matching property.

**Stabilization Proof.**
It is fairly easy to show that the 1-bit matching protocol is stabilizing.
First we will show that all executions terminate.
Then we will show that all silent states belong to the invariant.
From the [protocol](../examplesoln/MatchRingOneBit.prot), we see that each `P[i]` has the following actions:
```
(              x[i]==1 && x[i+1]==1 --> x[i]:=0; )
( x[i-1]==0 && x[i]==0 && x[i+1]==0 --> x[i]:=1; )
```

We can analyze the actions to see that the protocol is livelock-free.
The first action of `P[i]` removes cases of 2 consecutive 1 values by changing the left value to 0.
This may enable the second action of `P[i-1]`.
The second action of `P[i]` removes cases of 3 consecutive 0 values by changing the middle value to 1.
If `P[i]` executes its section action neither it or its neighbors is enabled!
Therefore, actions may propagate by changing consecutive 1s to 0s, and some of the resulting 0s may toggle back to 1s, but the 1s will not be consecutive.

Clearly the silent states are those where no 2 consecutive 1s exist and no 3 consecutive 0s exist.
That means a 1 must occur at least every 3 values and will be followed by a 0.
We can therefore interpret a 1 value followed by a 0 value to mean that the edge between the two values is selected.
These edges are not consecutive and at least on of every 3 will be selected, therefore it is a maximal matching.
```
forall i <- Nat % N :
   x[i-1]==1 && x[i]==0               // P[i] matched with P[i-1]
|| x[i-1]==0 && x[i]==0 && x[i+1]==1  // P[i] is not matched
||              x[i]==1 && x[i+1]==0  // P[i] matched with P[i+1]
```

## 3-State Maximal Matching on a Ring {#sec:MatchRingThreeState}

**MatchRingThreeState.**
([spec](../examplespec/MatchRingThreeState.prot),
 [args](../examplesett/MatchRingThreeState.args),
 [soln](../examplesoln/MatchRingThreeState.prot))

Matching can also be reasoned about in terms of processes.
Allow each process `P[i]` in a ring to point to `P[i-1]`, itself, or `P[i+1]`.
Let these directions be denoted by having `P[i]`'s variable `m[i]` have a value of `L`, `S`, and `R` respectively.
The processes form a maximal matching when they point to each other or themselves, but no two neighboring processes can both point to themselves.
```
forall i <- Nat % N :
   m[i-1]==R && m[i]==L               // P[i] pointing to P[i-1] and P[i-1] pointing back
|| m[i-1]==L && m[i]==S && m[i+1]==R  // P[i] pointing to itself and neighbors pointing away
||              m[i]==R && m[i+1]==L  // P[i] pointing to P[i+1] and P[i+1] pointing back
```

One stabilizing protocol has the actions:
```
( m[i-1]==2 && m[i]!=0 && m[i+1]!=0 --> m[i]:=0; )
( m[i-1]!=2 && m[i]!=1 && m[i+1]==2 --> m[i]:=1; )
( m[i-1]!=2 && m[i]!=2 && m[i+1]!=2 --> m[i]:=2; )
```

### Deriving 1-Bit Protocol from 3-State Protocol {#sec:MatchRingOneBit}

**MatchRingOneBit.**
([spec](../examplespec/MatchRingOneBit.prot),
 [synt](../examplesynt/MatchRingOneBit.prot),
 [soln](../examplesoln/MatchRingOneBit.prot))

This section explains shadow/puppet synthesis as a special case of superposition.
In the [previous section](#sec:MatchRing), we saw that a protocol could achieve a matching using only 1 bit per process.
How could this be derived?
From the above 3-state protocol, it seems that each process needs to be able to point in 3 directions.

Give each process `P[i]` a binary `x[i]` variable to perform the protocol along with a ternary `m[i]` variable used to specify the invariant.
Furthermore, `P[i]` is given read access to `x[i-1]` and `x[i+1]`, but it cannot read `m[i-1]` or `m[i+1]`.

We use the previous section's invariant on the underlying `m` variables.
Since processes only know their own `m` values, the protocol is forced to use `x` values to negotiate appropriate `m` values.
Our invariant style (the `((future & silent) % puppet)` style) allows closure to be violated for some (but not all) valuations of `x` variables.

See: [examplespec/MatchRingOneBit.prot](../examplespec/MatchRingOneBit.prot)

From synthesis, [one of the protocols](../examplesynt/MatchRingOneBit.prot) we get is the following.
```
( x[i-1]==1 && x[i]==1 && x[i+1]==1 --> x[i]:=0; m[i]:=L; )
( x[i-1]==0 && x[i]==1 && x[i+1]==1 --> x[i]:=0; m[i]:=S; )
( x[i-1]==0 && x[i]==0 && x[i+1]==0 --> x[i]:=1; m[i]:=R; )

( x[i-1]==1 && x[i]==0              && m[i]!=L --> m[i]:=L; )
( x[i-1]==0 && x[i]==0 && x[i+1]==1 && m[i]!=S --> m[i]:=S; )
( x[i-1]==0 && x[i]==1 && x[i+1]==0 && m[i]!=R --> m[i]:=R; )
```

From here, we can create the 1-bit matching protocol on the `x[i]` variables without the `m[i]`s.
The first three actions of the synthesized protocol change `x[i]` and are therefore used as actions in our 1-bit matching protocol, discarding changes to `m[i]`.
```
( x[i-1]==1 && x[i]==1 && x[i+1]==1 --> x[i]:=0; )
( x[i-1]==0 && x[i]==1 && x[i+1]==1 --> x[i]:=0; )
( x[i-1]==0 && x[i]==0 && x[i+1]==0 --> x[i]:=1; )
```

The invariant is all states where the `x[i]` values don't change (see the last three actions above).
```
forall i <- Nat % N :
   x[i-1]==1 && x[i]==0               // P[i] pointing to P[i-1] and P[i-1] pointing back
|| x[i-1]==0 && x[i]==0 && x[i+1]==1  // P[i] pointing to itself and neighbors pointing away
|| x[i-1]==0 && x[i]==1 && x[i+1]==0  // P[i] pointing to P[i+1] and P[i+1] pointing back
```
Each of these cases in the disjunction corresponds to `P[i]` pointing to `P[i-1]`, itself, and `P[i+1]` respectively.
We know this by looking at how `m[i]` is changed to be `m[i]:=L`, `m[i]:=S`, and `m[i]:=R` in the synthesized protocol.

Note that the third case in the disjunction can be simplified from `x[i-1]==0 && x[i]==1 && x[i+1]==0` to `x[i]==1 && x[i+1]==0` since if the formula holds for `P[i]` and the system is in the invariant, then the first or second cases in the disjunction must hold for `P[i-1]` (hence, `x[i-1]=0`).

Putting this all together, we get: [examplesoln/MatchRingOneBit.prot](../examplesoln/MatchRingOneBit.prot)

### Using Shadow/Puppet Variables

Shadow variables are variables that cannot be used in the guard of any actions.
Therefore, to reliably obtain a protocol that is free of `m` variables, we must mark them as shadow variables by replacing `direct` with `shadow` in the [specification](../examplespec/MatchRingOneBit.prot).
This is essentially what is done in the [previous section](#sec:MatchRing), but a more convenient invariant is used.

## Segmented Ring {#sec:SegmentRing}

**SegmentRing.**
([spec](../examplespec/SegmentRing.prot),
 [args](../examplesett/SegmentRing.args),
 [synt](../examplesynt/SegmentRing.prot))

This is a problem similar to matching where a ring is segmented into chains.
