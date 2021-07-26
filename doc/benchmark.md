
# Synthesis Benchmarks

These results have been obtained on the **Superior** cluster at Michigan Tech (CPU: Intel E5-2670 2.60 GHz).
Settings are tuned to obtain protocols that appear to be generalizable.
That is, the resulting protocols are stabilizing for more processes than were considered during synthesis, but we do not prove that they are stabilizing for arbitrary numbers of processes.

| Protocol | Protocol Processes | Compute Processes | Compute Time | Peak Memory | Notes |
| -------- |:------------------:|:-----------------:|:------------:|:-----------:| ----- |
| [3-State Token Ring (Dijkstra)](../example/TokenPassing.html#sec:TokenRingThreeState) | [2--5](../examplesett/TokenRingThreeState.args) | 4 | 9.300s | 90.6 MB | Bidirectional ring. |
| [3-State Token Chain](../example/TokenPassing.html#sec:TokenChainThreeState) | [2--5](../examplesett/TokenChainThreeState.args) | 4 | 29.310s | 101.3 MB | Bidirectional chain (line). Allows actions that do not pass a token. |
| [4-State Token Chain](../example/TokenPassing.html#sec:TokenChainDijkstra) | [2--4](../examplesett/TokenChainDijkstra.args) | 6.548s | 66.4 MB | Bidirectional chain (line). |
| [5-State Token Ring](../example/TokenPassing.html#sec:TokenRingFiveState) | [2--9](../examplesett/TokenRingFiveState.args) | 8 | 12m54.684s | 153.4 MB |
| [6-State Token Ring](../example/TokenPassing.html#sec:TokenRingSixState) | [2--9](../examplesett/TokenRingSixState.args) | 4 | 20m17.846s | 266.6 MB | Allows actions that do not pass a token. |
| [3-Bit Token Ring (Gouda and Haddix)](../example/TokenPassing.html#sec:TokenRingThreeBit) | [2--9](../examplesett/TokenRingThreeBit.args) | 4 | 17m17.564s | 495.7 MB | Allows actions that do not pass a token. |
| [Odd-Sized Ring Orientation (Hoepman)](../example/Orientation.html#sec:OrientRingOdd) | [3,5,7](../examplesett/OrientRingOdd.args) | 4 | 34m05.289s | 104.7 MB | Only works for rings of odd-size. Not necessarily silent. |
| [Ring Orientation](../example/Orientation.html#sec:OrientRing) | [2--9](../examplesett/OrientRing.args) | 16 | 13m52.606s | 169.6 MB | Works with synchronous and asynchronous schedulers. |
| [Daisy Chain Orientation](../example/Orientation.html#sec:OrientDaisy) | [2--6](../examplesett/OrientDaisy.args) | 1 | 2m01.112s | 78.8 MB | Works on ring and chain topologies. |
| Stop-and-Wait | [2](../examplesett/StopAndWait.args) | 4 | 3m03.217s | 101.9 MB | Ternary version of the alternating-bit protocol. |
| [3-Coloring on Ring](../example/Coloring.html#sec:ColorRing) | [2--5](../examplesett/ColorRing.args) | 1 | 0.067s | 38.5 MB | |
| [Distributed 3-Coloring on Ring](../example/Coloring.html#sec:ColorRingDistrib) | [2--4](../examplesett/ColorRingDistrib.args) | 1 | 24.786s | 75.7 MB | A 1-capacity buffer between each process. Uses randomization. |
| [Distance-2 5-Coloring on Ring](../example/Coloring.html#sec:ColorRingLocal) | [3--5](../examplesett/ColorRingLocal.args) | 4 | 7m24.513s | 810.8 MB | Uses randomization. |

![NSF logo](http://www.nsf.gov/images/logos/nsf1.gif)\
This work is sponsored by the NSF grant CCF-1116546.\
Any opinions, findings, and conclusions or recommendtions expressed in this material are those of the authors and do not necessarily reflect the views of the National Science Foundation.

