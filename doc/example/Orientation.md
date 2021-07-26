
\title{Orientation on Odd-Sized Rings}
%\author{}
\date{}

\begin{document}

\tableofcontents

\section{Ring Orientation}
\label{sec:OrientRing}

\quicksec{OrientRing}
(\href{\examplespec/OrientRing.prot}{spec},
\href{\examplesett/OrientRing.args}{args},
\href{\examplesoln/OrientRing.prot}{soln})

\section{Odd-Sized Ring Orientation}
\label{sec:OrientRingOdd}

\quicksec{OrientRingOdd}
(\href{\examplespec/OrientRingOdd.prot}{spec},
\href{\examplesett/OrientRingOdd.args}{args},
\href{\examplesoln/OrientRingOdd.prot}{soln})

The \ilfile{examplespec/OddOrientRing.prot} file specifies a bidirectional ring topology where processes wish to agree with each other on a direction around the ring.
The topology is taken from the paper by Hoepman titled \textit{Uniform Deterministic Self-Stabilizing Ring-Orientation on Odd-Length Rings}.

\subsection{Problem Instance}

\codeinputlisting{../../../examplespec/OrientRingOdd.prot}

Each process \ttvbl{P[i]} reads \ttvbl{color[i-1]}, \ttvbl{color[i+1]}, \ttvbl{phase[i-1]}, and \ttvbl{phase[i+1]} and writes \ttvbl{color[i]}, \ttvbl{phase[i]}, \ttvbl{way[2*i]}, and \ttvbl{way[2*i+1]}.

Eventually we want all the \ttvbl{way[2*i]} values to equal each other and differ from the \ttvbl{way[2*i+1]} values.
That is, we want each process to agree on a direction.

The \ttvbl{color} and \ttvbl{phase} variables are labeled as \ilcode{puppet} because we allow the protocol to use them to achieve convergence.

The invariant is labeled as \ilcode{((future & shadow) % puppet)} since we only require closure within a new invariant $I'$ rather than $I$.
Also, the behavior of the protocol within the new invariant $I'$ must be the same as the underlying (i.e., shadow) protocol within $I$.

\subsection{Stabilizing Version}

\codeinputlisting{../../../examplesoln/OrientRingOdd.prot}

\section{Daisy Chain Orientation}
\label{sec:OrientDaisy}

\quicksec{OrientDaisy}
(\href{\examplespec/OrientDaisy.prot}{spec},
\href{\examplesett/OrientDaisy.args}{args},
\href{\examplesynt/OrientDaisy.prot}{synt},
\href{\examplesoln/OrientDaisy.prot}{soln})

\end{document}

