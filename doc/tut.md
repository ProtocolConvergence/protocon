
\title{Tutorial}
%\author{}
\date{}

\begin{document}

Welcome to the Protocon tutorial!
If you haven't already, please download the latest Linux binary from \href{index.html}{the main page}.
Next, open up a terminal, navigate to the download location, unzip it, and enter the resulting directory.
\begin{code}
cd ~/Downloads
unzip protocon-bin-YYYYMMDD.zip
cd protocon-bin-YYYYMMDD
\end{code}
Where \ilcode{YYYYMMDD} is the current version number.

%Tip: You can copy and paste commands by highlighting the text and middle-clicking in a terminal.
%(Though it's not always the best thing to do \href{http://thejh.net/misc/website-terminal-copy-paste}{security-wise}).

\tableofcontents


\section{Coloring}

The file \href{\examplespec/ColorRing.prot}{examplespec/ColorRing.prot} specifies a bidirectional ring topology where each process wishes to obtain a different value than its two neighbors.
Each process has $3$ colors to choose from.
We can synthesize actions for this protocol by issuing the command:
\begin{code}
./bin/protocon -x examplespec/ColorRing.prot -o tmp/color.prot
\end{code}
And we can verify that the resulting protocol is stabilizing:
\begin{code}
./bin/protocon -verify -x tmp/color.prot
\end{code}

Remove the file
\begin{code}
rm tmp/color.prot
\end{code}
and open the original specification in a GUI.
\begin{code}
./bin/protocon-gui examplespec/ColorRing.prot
\end{code}

The GUI allows us to perform synthesis and verification in the same way.
First, change the output file name to \ilfile{tmp/color.prot}.
Next, push the \ilkey{Synthesize} button.
After success, close the pop-up window and open the resulting protocol file by pushing the \ilkey{Open} button below the output file name or using the \ilkey{File} menu.
With the protocol file opened, verify it by pushing the \ilkey{Verify} button.

The GUI also lets us manually walk through a protocol's execution.
To do this, push the \ilkey{Explore} button.
This new window shows the system's current state (i.e., \ilkey{Values} of all variables), all possible states reached by a single process acting (i.e., \ilkey{Forward} transitions), and all possible previous states (i.e., \ilkey{Backward} transitions).
The initial state has all $x$ values set to $0$, which can be changed by selecting a variable and typing a number.
Alternatively, the \ilkey{Randomize State} button will randomize all values.

The exploration window also shows if the current state is within the specified invariant (all neighboring processes have different colors), is silent (no process will act), or is part of a cycle (can be reached infinitely often).
Cycle detection can be time consuming for large systems, therefore one must push the \ilkey{Find Cycles} button for cycle information.
We can also \ilkey{Restrict} our view to a combination of these these predicates.
Try clicking the \ilkey{false} radio button for the \ilkey{invariant} predicate and then press the \ilkey{Randomize State} button.
We are brought to a state where some process shares the same color as its neighbor.
The forward and backward transitions are also restricted.
To see this, click one of the \ilkey{Forward} transitions or the \ilkey{Step Forward} button a few times until the state no longer changes.
The system has not yet formed a valid coloring!
Clicking the \ilkey{or} or \ilkey{true} radio button for the \ilkey{invariant} predicate reveals a final transition (or two) to reach the invariant.


\section{Maximal Matching}

The file \href{\examplespec/MatchRingThreeState.prot}{examplespec/MatchRingThreeState.prot} specifies a bidirectional ring topology where each process wishes to match with one of its neighbors.
When \ttvbl{x[i]} is $0$ or $2$, process \ttvbl{P[i]} is pointing to \ttvbl{P[i-1]} or \ttvbl{P[i+1]} respectively.
Two processes are matched together when they point to each other.
Sometimes a perfect matching is impossible, so any process \ttvbl{P[i]} can remain unmatched (with \ttvbl{x[i]} equaling $1$) when both of its neighboring processes are matched.

We can synthesize actions for this protocol on a ring of size $4$ by issuing the command:
\begin{code}
./bin/protocon -x examplespec/MatchRingThreeState.prot -o tmp/match.prot -def N 4
\end{code}
%Note: To avoid mistakes, prefer to place the \ilkey{-def} flag after the \ilkey{-x} flag.
%When the definition will affect variable domains, prefer to edit the file directly or place \ilkey{-def} before \ilkey{-x}.
%(Protocon will catch these problems and advise you.)

Does the resulting protocol stabilize on ring of size $3$?
\begin{code}
./bin/protocon -verify -x tmp/match.prot -def N 3
\end{code}
Probably not. Let's investigate the issue.

Open the file in a GUI.
\begin{code}
./bin/protocon-gui tmp/match.prot
\end{code}
Change the constant \ttvbl{N} to $3$ by modifying the text to have \ilcode{constant N := 3;} on the first line.

To investigate the deadlock, click \ilkey{Explore} and select \ilkey{false} for the \ilkey{invariant} predicate and \ilkey{true} for the \ilkey{silent} predicate.
Click the \ilkey{Randomize State} button to find a deadlock state.
Close the GUI.

To fix this, we must synthesize a protocol that stabilizes for rings of multiple sizes.
Let's do this for rings of size $3$, $4$, and $5$.
\begin{code}
./bin/protocon -x examplespec/MatchRingThreeState.prot -o tmp/match.prot -def N 3 -param N 4 -param N 5
\end{code}
%Note: Using the \ilkey{-param} flag when it affects variable domains will result in an error.


\section{Sum-Not-2}

The file \href{\examplespec/SumNotTwo.prot}{examplespec/SumNotTwo.prot} specifies a unidirectional ring topology where we do not want the sum of any two consecutive values to equal $2$.
Open the file in the GUI and add the following three actions at the end of the process block:
\begin{code}
  puppet action:
    ( x[i-1]==0 && x[i]==2 --> x[i]:=0; )
    ( x[i-1]==1 && x[i]==1 --> x[i]:=2; )
    ( x[i-1]==2 && x[i]==0 --> x[i]:=2; )
    ;
\end{code}

Try the following:
\begin{enumerate}
\item Use the exploration window to find a livelock (a cycle outside of the invariant).
\item What is happening in the livelock?
\item How can the last action be modified in order to remove the livelock?
 \begin{itemize}
 \item Hint: Remove the last action and run synthesis.
 \end{itemize}
\end{enumerate}


\section{Sum-Not-Odd}

Consider a sum-not-odd protocol on a unidirectional ring that stabilizes to states where the sum of any two consecutive numbers is even.
We will see how Protocon can optimize performance and also help with manual construction of a protocol.

Try the following:
\begin{enumerate}
\item Specify the sum-not-odd problem using \href{\examplespec/SumNotTwo.prot}{examplespec/SumNotTwo.prot} as a template.
 \begin{itemize}
 \item Use the mod operator \%.
 \item Keep variable domains at size $M=3$.
 \end{itemize}
\item Synthesize a sum-not-odd protocol that stabilizes on rings of size $2$, $3$, $4$, and $5$.
\item Verify that it stabilizes on a ring of size $8$.
 \begin{itemize}
 \item Note the number reported after \ilcode{Max async layers to fixpoint:}, this is the worst-case number of steps to converge on a ring of size $8$.
 \end{itemize}
\item Synthesize a sum-not-odd protocol again for $N=2,3,4,5$, and add the \ilflag{-optimize} flag to the command.
\item Verify that the resulting protocol stabilizes on a ring of size $8$.
 \begin{itemize}
 \item Note that the worst-case number of convergence steps is smaller than before.
 \end{itemize}
\end{enumerate}

We would now like to create a general sum-not-odd protocol for any variable domain of size $M$.
One problem is that randomization is used during synthesis, which gives a random-looking protocol.
\begin{enumerate}
\item Synthesize a sum-not-odd protocol again for $N=2,3,4,5$, and add the \ilflag{-optimize} and \ilflag{-no-random} flags to the command.
 \begin{itemize}
 \item Save this result somewhere.
 \end{itemize}
\item Change variable domains to $M=4$ in the file.
\item Repeat step $1$.
\item Change variable domains to $M=5$ in the file.
\item Repeat step $1$.
\item Looking at these protocols, can you devise a sum-not-odd protocol that stabilizes for any domain size $M$?
\end{enumerate}


\section{Maximal Matching with Shadow/Puppet Synthesis}

In graph theory, maximal matching is defined in terms of edges rather than nodes (i.e., processes).
We would like to do the same, but placing a variable between each process is unrealistic in a distributed system.

Using shadow puppetry as a metaphor, we can split the concept of desired behavior away from implementation.
We want to cast a particular shadow upon a screen by placing a well-crafted puppet between the screen and a light.
Instead of building the puppet ourselves, we can ask a clever puppeteer to build it for us.
In this metaphor, the clever puppeteer is Protocon, the shadow is our desired invariant and behavior, the puppet is the synthesized protocol.

The \href{\examplespec/MatchRing.prot}{examplespec/MatchRing.prot} file uses this technique to specify matching on edge variables where:
\begin{enumerate}
\item No two adjacent edges can be selected.
\item At least one of every three consecutive edges must be selected.
\end{enumerate}
Edge variables are declared with the \ilkey{shadow} keyword since they will not exist in the implementation, therefore their values must be derived from the \ilkey{puppet} variables.
Generally, the invariant and behavior constraints should only apply for some values of puppet variables, so these constraints are specified as \ilcode{((future & silent) % puppet)} rather than the usual \ilcode{(future & silent)}.

The \href{\examplesynt/MatchRing.prot}{examplesynt/MatchRing.prot} contains a synthesized protocol for this system.
Notice that the \ttvbl{e} values are fully derived from \ttvbl{x} values.
Therefore, the protocol can be implemented without \ttvbl{e} values at all!
See \href{\examplesoln/MatchRingOneBit.prot}{examplesoln/MatchRingOneBit.prot} for this transformation.


\section{Next Steps}

This concludes the tutorial.
To see what else is possible (beyond silent protocols on rings), browse our ever-growing list of example protocols.
For a complete feature list (such as the \ilflag{-parallel} or \ilflag{-x-args} options), browse the manual page.

\begin{itemize}
\item \url{example/index.html} - List of example files.
\item \url{legit.html} - More ways to specify the invariant and behavior.
\item \url{man.html} - Manual page.
\end{itemize}

Email the author@mtu.edu, where the author is apklinkh, with questions/bugs/requests.

\end{document}

