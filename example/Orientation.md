
# Orientation on Odd-Sized Rings

## Ring Orientation {#sec:OrientRing}

**OrientRing.**
([spec](../examplespec/OrientRing.prot),
 [args](../examplesett/OrientRing.args),
 [soln](../examplesoln/OrientRing.prot))

## Odd-Sized Ring Orientation {#sec:OrientRingOdd}

**OrientRingOdd.**
([spec](../examplespec/OrientRingOdd.prot),
 [args](../examplesett/OrientRingOdd.args),
 [soln](../examplesoln/OrientRingOdd.prot))

The `examplespec/OddOrientRing.prot` file specifies a bidirectional ring topology where processes wish to agree with each other on a direction around the ring.
The topology is taken from the paper by Hoepman titled *Uniform Deterministic Self-Stabilizing Ring-Orientation on Odd-Length Rings*.

### Problem Instance

See: [examplespec/OrientRingOdd.prot](../examplespec/OrientRingOdd.prot)

Each process `P[i]` reads `color[i-1]`, `color[i+1]`, `phase[i-1]`, and `phase[i+1]` and writes `color[i]`, `phase[i]`, `way[2*i]`, and `way[2*i+1]`.

Eventually we want all the `way[2*i]` values to equal each other and differ from the `way[2*i+1]` values.
That is, we want each process to agree on a direction.

The `color` and `phase` variables are labeled as `puppet` because we allow the protocol to use them to achieve convergence.

The invariant is labeled as `((future & shadow) % puppet)` since we only require closure within a new invariant *I'* rather than *I*.
Also, the behavior of the protocol within the new invariant *I'* must be the same as the underlying (i.e., shadow) protocol within *I*.

### Stabilizing Version

See: [examplesoln/OrientRingOdd.prot](../examplesoln/OrientRingOdd.prot)

## Daisy Chain Orientation {#sec:OrientDaisy}

**OrientDaisy.**
([spec](../examplespec/OrientDaisy.prot),
 [args](../examplesett/OrientDaisy.args),
 [synt](../examplesynt/OrientDaisy.prot),
 [soln](../examplesoln/OrientDaisy.prot))

