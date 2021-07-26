
# Token Passing

Token passing systems are used for distributed mutual exclusion, where exactly one process has a *token* at any given time, and the token must be passed in order for other processes to have this privilege.
In the context of self-stabilization, the system may be in a state with multiple tokens, and it therefore must converge to having a single token.


## Dijkstra's Token Ring {#sec:TokenRingDijkstra}

**TokenRingDijkstra.**
([spec](../examplespec/TokenRingDijkstra.prot),
[args](../examplesett/TokenRingDijkstra.prot),
[soln](../examplesoln/TokenRingDijkstra.prot))

## 5-State Token Ring {#sec:TokenRingFiveState}

**TokenRing.**
([spec](../examplespec/TokenRing.prot),
[args](../examplesett/TokenRingFiveState.args),
[synt](../examplesynt/TokenRingFiveState.prot),
[soln](../examplesoln/TokenRingFiveState.prot) )

This is a unidirectional token ring that has 5 states per process.
Without using randomization, no smaller token ring exists.
Interestingly, we can still pass a token with every action in the invariant.

## 6-State Token Ring {#sec:TokenRingSixState}

**TokenRingSixState.**
([spec](../examplespec/TokenRingSuperpos.prot),
[args](../examplesett/TokenRingSixState.args),
[synt](../examplesynt/TokenRingSuperpos.prot),
[soln](../examplesoln/TokenRingSixState.prot))

## 3-Bit Token Ring {#sec:TokenRingThreeBit}

**TokenRingThreeBit.**
([spec](../examplespec/TokenRingThreeBit.prot),
[args](../examplesett/TokenRingThreeBit.args),
[synt](../examplesynt/TokenRingThreeBit.prot),
[soln](../examplesoln/TokenRingThreeBit.prot))

This section shows how to synthesize a self-stabilizing token ring using the same topology given by
Gouda and Haddix in *The Stabilizing Token Ring in Three Bits*.
It uses 8 states per process.
Not every action in the invariant passes a token, which causes a noticeable lag for larger rings.

### Problem Instance

See: [examplespec/TokenRingThreeBit.prot](../examplespec/TokenRingThreeBit.prot)

Each process can read `e[i-1]` and `t[i-1]` and can write `e[i]`, `t[i]`, and `ready[i]`.
There is a distinguished process `Bot` that can act differently than the others.

The invariant is specified as all states where exactly one process has a token.
`Bot` is defined to have a token when `t[0] == t[N-1]` and each other `P` process has a token when `t[i] != t[i-1]`.

With the shadow actions, we enforce that processes act like Dijkstra's token ring on one bit (the `t` variables).

### Synthesis

Let's try to find a stabilizing token ring using three bits on a ring of size 5.
```
protocon -x examplespec/TokenRingThreeBit.prot -o tmp/3bit.prot -def N 5
```

Is the protocol stabilizing on a ring of size 3?
```
protocon -verify -x tmp/3bit.prot -def N 3
```

How about of size 4 or 6?
```
protocon -verify -x tmp/3bit.prot -def N 4
protocon -verify -x tmp/3bit.prot -def N 6
```

Probably not.
Let's try again, taking those sizes into account!
```
protocon -x examplespec/TokenRingThreeBit.prot -o tmp/3bit.prot -def N 5 -param N 3 -param N 4 -param N 6
```

But what if we want to search up to size 7, but it takes too long check a system of that size at each decision level?
Use the `-no-partial` flag to just verify the protocol on that system after finding a protocol that is self-stabilizing for all smaller sizes.
```
protocon -x examplespec/TokenRingThreeBit.prot -o tmp/3bit.prot -def N 5 -param N 3 -param N 4 -param N 6 -param [ -def N 7 -no-partial ]
```

### Stabilizing Version

See: [examplesoln/TokenRingThreeBit.prot](../examplesoln/TokenRingThreeBit.prot)

## 3-State Token Ring (Dijkstra) {#sec:TokenRingThreeState}

**TokenRingThreeState.**
([spec](../examplespec/TokenRingThreeState.prot),
[args](../examplesett/TokenRingThreeState.args),
[synt](../examplesynt/TokenRingThreeState.prot),
[soln](../examplesoln/TokenRingThreeState.prot))

This ring is bidirectional, and passes the token back-and-forth.
Every action in the invariant passes a token.

## 3-State Token Chain {#sec:TokenChainThreeState}

**TokenChainThreeState.**
([spec](../examplespec/TokenChain.prot),
[args](../examplesett/TokenChainThreeState.args),
[synt](../examplesynt/TokenChain.prot),
[soln](../examplesoln/TokenChainThreeState.prot))

This is a bidirectional chain that passes the token back-and-forth.
It uses 3 states per process.
Not every action in the invariant passes a token, but the actions that do not pass the token can be run in parallel with the token-passing ones, so the performance hit is small.


## 4-State Token Chain (Dijkstra) {#sec:TokenChainDijkstra}

**TokenChainDijkstra.**
([spec](../examplespec/TokenChainDijkstra.prot),
[synt](../examplesynt/TokenChainDijkstra.prot),
[soln](../examplesoln/TokenChainDijkstra.prot))

This is a bidirectional chain that passes the token back-and-forth.
It uses 4 states per process.
It converges quickly and every action in the invariant passes the token.

