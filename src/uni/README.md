
# Unidirectional Ring Analysis

This directory contains the source for tools that analyze unidirectional rings of symmetric processes.
It is a fairly niche use case, so they are built in `./bld/uni/` relative to the top-level directory.

* `generate` -- Find canonical examples of protocols that cannot be proved silent or shown to have a livelock by searching up to a certain cutoff.
* `classify` -- Try to classify a given protocol as silent or having a livelock by searching up to a certain cutoff for the period. This classification is more powerful (and more expensive) than the one used by `generate`.
* `xlate` -- Write different types of files corresponding to a given input protocol.
* `aperiodic` -- Output a hard-to-verify unidirectional ring protocol that is derived from an aperiodic Wang tileset.
* `synthesize` -- Synthesize stabilization for a given unidirectional ring spec (as a `.prot` file).

## How to Run

The following command generates a few small interesting protocols using domain size 4.
```
./bld/uni/generate -domsz 4 -cutoff 8
```

