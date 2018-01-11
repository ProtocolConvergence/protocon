
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
The `-cutoff 8` flag means that the output protocols will not have a livelock that can be characterized by a tiling with an 8x8 periodic block or smaller.
```
./bld/uni/generate -domsz 4 -cutoff 8
```
The outputs of this command are protocol ID strings, which both `classify` and `xlate` use for input.
For example, the `classify` tool can be used to analyze a protocol using higher cutoffs.
The following command analyzes one of the generated protocols, but it uses a cutoff of 20.
It should find a livelock of period 9.
```
./bld/uni/classify 20 -id 57XHa__A
```
To see what this protocol actually is, use `xlate` as follows.
```
./bld/uni/xlate -id 57XHa__A -o-prot
```

## Options

### Generate

* `-domsz <domain size>` -- Number of states per process. Required unless the `-init` flag is given.
* `-cutoff <limit>` -- Maximum width and height of a tile block that we use to check for livelocks.
* `-bdd` -- Use binary decision diagrams for livelock detection. This effectively removes the tile block's height constraint when detecting livelocks. It is generally slower, so prefer to use the `classify` tool for this kind of analysis.
* `-nw-disabling` -- Along with enforcing self-disabling processes, which means the corresponding tilesets are W-disabling, also enforce N-disabling tilesets. The N-disabling property has no real meaning for protocols, but it gives a nice symmetry to the tileset constraints.
* `-o <file>` -- Write protocol IDs to `<file>` instead of stdout.
* `-bfs <depth>` -- Search only to a certain depth, writing all partial protocols at `<depth>` to stdout.
* `-init <ID>` -- Search from the partial protocol identified by `<ID>`. The only useful way to get such an ID is using the `-bfs` flag.

### Classify

The `classify` tool tries to prove whether given protocols are silent or have livelocks.

* `[<min period>] <max period>` -- A range to use for classifying protocols (minimum period is optional). This is more powerful than the `-cutoff` flag used by `generate` because the period is only the width of a periodic tile block. We will detect livelocks of any periodic block height.
* `-nobdd` -- Don't use binary decision diagrams for classification. This effectively makes the given `<max period>` act as the cutoff used in `generate`.
* `-id <ID>` -- The protocol to classify. If this option is omitted, then IDs are read from stdin.


### Translate

The `xlate` tool outputs many file formats from a (cryptic) protocol ID string.

* `-id <ID>` -- The protocol to classify. If neither `-id` nor `-x-list` are given, then one ID is read from stdin.
* `-x-list [<file>]` -- Read the protocol as a list of action triples instead of an ID.
* `-domsz <domain size>` -- Override the number of states per process. Can only be used with `-x-list`.
* `-o-id [<file>]` -- Write the protocol as an ID.
* `-o-prot [<file>]` -- Write the protocol in a format that can be read by Protocon. The `<file>` defaults to stdout  if `-o-prot` is the last argument given on the command line.
* `-o-graphviz [<file>]` -- Write the propagation graph in graphviz format. Use `dot` to make an image out of it.
* `-o-svg-livelock [<file>]` -- Write an SVG image showing the periodic tile block that characterizes a livelock. Use the `-cutoff` flag with this. If no livelock is found, then no file is written.
* `-cutoff <limit>` -- Maximum width and height of a tile block that we use to check for livelocks. Only useful in conjunction with the `-o-svg-livelock` flag.

