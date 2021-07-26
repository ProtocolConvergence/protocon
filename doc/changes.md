
\section{Release Notes}

\textbf{2015.10.20}
\begin{itemize}
\item Benchmarks and updates to documentation
\end{itemize}
\textbf{2016.07.05}
\begin{itemize}
\item Prefer new syntax over \ilcode{Nat % N} syntax
\end{itemize}
\textbf{2015.09.29}
\begin{itemize}
\item Add dining cryptographers, dining philosophers, and stop-and-wait examples
\item Allow actions that are not self-disabling when a self-disabling version violates safety
\item Make synthesis feasible for synchronous systems
\item Fix crash when optimizing using MPI
\item Fix \ilcode{-=>} operator when used with random write variables, and change it to automatically randomize unassigned ones
\item Fix \ilcode{-=>} operator to not affect the guard for pure shadow variables
\item New \ilcode{random read:} access to variables for probabilistic stabilization
\item New \ilcode{(future & closed)} keyword for stabilization without enforcing a specific protocol behavior
\end{itemize}
\textbf{2015.04.23}
\begin{itemize}
\item New \ilcode{random write:} access to variables for probabilistic stabilization
\item New \ilcode{(future & future silent)} and \ilcode{(future & future shadow)} keywords for convergence to any subset of the invariant
\item Daisy chain orientation example
\item Can implicitly remove self-loops by using \ilcode{-=>} in place of \ilcode{-->}
\item New \ilcode{min(a,b)} and \ilcode{max(a,b)} functions
\end{itemize}
\textbf{2015.01.16}
\begin{itemize}
\item Introduce \ilcode{active shadow} which can be substituted for \ilcode{shadow} to prevent shadow self-loops
\item Change \ilcode{permit:} semantics to make more intuitive sense
\item More examples and documentation
\end{itemize}
\textbf{2014.12.21}
\begin{itemize}
\item New support for \ilcode{shadow} variables
\item Use .prot file extension
\item MPI version now supports protocol optimization via the \ilflag{-optimize} flag
\item When using puppet variables, enforce a silent protocol with \ilcode{future silent;} line
\end{itemize}
\textbf{2014.09.12}
\begin{itemize}
\item New \ilcode{permit:} keyword to complement \ilcode{forbid:}
\item New \ilcode{(assume & closed)} keyword to restrict initial states
\item New \ilflag{-optimize} flag for finding an optimal protocol (in interleaved steps)
\item New \ilcode{(future & silent)} or \ilcode{(future & shadow)} syntax for invariants (see examples)
\item Putting a \ilflag{-def} before (but not after) \ilflag{-x} in the argument list affects the initial file read and candidate actions
\item More examples!
\item Substantially more quality control and testing, associated bug fixes
\end{itemize}
\textbf{2014.05.24}
\begin{itemize}
\item File reorganization
\item Preserve locally-conjunctive invariants
\end{itemize}
\textbf{2014.04.26}
\begin{itemize}
\item Serial search is now the default mode
\item Improved packaging
\item Improved file reading, still much room to improve
\item Verification in GUI
\end{itemize}
\textbf{2014.01.31}
\begin{itemize}
\item Symmetry can be enforced across sets of variables.
\item GUI gets a state exploration mode.
\item Can now mark actions as forbidden. Synthesis cannot use them for recovery.
\item Improve Promela model output.
\item More testing and bug fixes.
\end{itemize}
\textbf{2013.11.19}
\begin{itemize}
\item Fix output format when multiple variables are used.
\item Add ring orientation example
\end{itemize}

