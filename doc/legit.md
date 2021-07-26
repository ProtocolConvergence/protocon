
# Legitimate States and Behavior

## Defining the Invariant

Let's define a predicate for the system where all colors in the ring are distinct.
```
predicate I := (forall i <- Nat % N : c[i-1]!=c[i]);
```

Since we will use *I* as an invariant, it must be defined with shadow or direct variables (not puppet variables).

## Convergence and Behavior

Stabilization can be defined as both convergence and closure.
That is, a system should eventually reach *I* and remain within *I*.
This is generally too relaxed to be useful, but it is supported by writing the following in a `.prot` file:
```
(future & closed) (I);
```

We often want to specify how the protocol behaves within the invariant.
The simplest case is that of silent protocols.
Here we say the protocol should reach the invariant *I* and no actions should execute within *I*.
This is written as:
```
(future & silent) (I);
```

When there is shadow protocol defined (using `shadow action:` statements in process definitions), we can enforce that it is executed within *I*.
Puppet variables are allowed to be changed in any way, but shadow (and direct) variables must eventually change.
That is, some transitions in the protocol may not change any shadow variables, which will appear as a self-loop in the shadow protocol.
```
(future & shadow) (I);
```
If no shadow protocol is defined, this statement allows any finite or infinite executions within the invariant provided that the shadow variables are not changed.

Allowing shadow self-loops within *I* is undesirable since they delay operation of the shadow protocol.
These can be forbidden by forcing all transitions in *I* to correspond with transitions in the shadow protocol.
Write this as:
```
(future & active shadow) (I);
```
Note that the shadow protocol must not have deadlocks.


## Eventual Closure

Sometimes it is okay to find a protocol that stabilizes to some invariant *I'* that is a subset of the original invariant *I*.
This is the method of adaptive programs as described in [Adaptive Programming](http://dx.doi.org/10.1109/32.92911) by Gouda and Herman.
The three invariant styles above can be stated with this notion of eventual closure:
```
(future & future silent) (I);
(future & future shadow) (I);
(future & future active shadow) (I);
```

**Note:** Always use this notation or the next section's notation when using pure `shadow` variables (not `direct` variables).
Shadow variables are assigned completely based on puppet (and direct) variables, so any nontrivial protocol will have transitions that leave *I*.
Therefore *I'* will need to be a proper subset of *I*.


## Modding out Puppet Variables

Sometimes we want to enforce that each state in *I* is kept within *I'* for at least some values of puppet variables.
That is, for every valuation of shadow (or direct) variables that satisfies *I*, a state exists in *I'* with the same valuation (but some arbitrary valuation of puppet variables).
In other words, we want *I* to equal *I'*, ignoring differences caused by puppet variables.

Semantics follow directly from the previous section.
To synthesize a protocol that is silent in some *I'*, we would write `(future & silent) (I_prime);` if we knew *I'*.
It can be difficult to determine *I'* manually, so we prefer to specify *I* and use a certain notation to say that *I=I'* *modulo* the puppet variables.
This is written as:
```
((future & silent) % puppet) (I);
```

Likewise, if we want to enforce execution of the shadow protocol within *I'* (i.e., `(future & shadow) (I_prime);`), we write:
```
((future & shadow) % puppet) (I);
```
This is the general constraint we used in [Synthesizing Self-stabilization through Superposition and Backtracking](http://dx.doi.org/10.1007/978-3-319-11764-5_18).

Finally, if we want to force all actions within *I'* to correspond with actions in the shadow protocol (i.e., `(future & active shadow) (I_prime);`), we write:
```
((future & active shadow) % puppet) (I);
```


## Eventual Behavior

In some cases, forcing silence or an active shadow protocol within the entire invariant *I'* is too strict.
Rather, we are often content to enforce these constraints on the protocol's eventual behavior.
This is done by an additional statement in the specification `.prot` file.
That is, the statements in this section are optional and are given in addition to lines such as `(future & shadow) (I);` or `((future & shadow) % puppet) (I);`.

When the shadow protocol is silent, we often want to enforce a silent protocol overall in order to minimize network traffic.
This is expressed by adding the following line:
```
future silent;
```
We use this in [examplespec/OrientRing.prot](../examplespec/OrientRing.prot) example where the invariant is defined as `(future & shadow) (I);`.
In this case, we desire a silent protocol, but the two alternative ways to define the invariant have deficiencies:
(1) `(future & silent) (I);` is too strict, and
(2) `((future & silent) % puppet) (I);` does not force *I'=I*, which disables some search optimizations.

When the shadow protocol is live, we often want the synthesized protocol to execute its actions exactly (i.e., eventually, every transition of the system corresponds to a shadow action).
This desire is for practicality - we want the service to respond quickly if no faults are occurring.
Write this as:
```
future active shadow;
```
We could use this in [examplespec/TokenRingSuperpos.prot](../examplespec/TokenRingSuperpos.prot) where the invariant is defined as `(future & shadow) (I);`.
Though it is not used in the example itself, we could add `future active shadow;` if we want every transition within the invariant to pass a token.
We would do this over simply defining the invariant do be active, since the alternative ways to define the invariant have deficiencies:
(1) `(future & active shadow) (I);` is too strict, and
(2) `((future & active shadow) % puppet) (I);` does not force *I'=I*, which disables some search optimizations.
