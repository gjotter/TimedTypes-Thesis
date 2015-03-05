%include polycode.fmt 
%format |-> = "\mapsto"
%format veca = "\vec a"
%format vecb = "\vec b"
%format delay1 ="\sigma_1"
%format delayx ="\sigma_x"
%format delay = "\sigma"
%format Delayx = "\Delta_x"
%format Delay1 = "\Delta_1"
%format mylang = "\lambda^{\rightarrow}_{\Delta}"
%format psin = "\psi. n."
%format < = "\langle"
%format > = "\rangle"
%format *> = ">"
%format <--> = "\leftrightarrow"
%format <- = "\leftarrow"
%format -!> = "\overset{!}{\rightarrow}"
%format \\ = "\lambda"
%format <==> = "\leftrightarrow"
%format <||> = "\langle || \rangle"
%format par = "\langle || \rangle"

\chapter{Related Work}
\todo[inline]{Following things we can discuss here: totality/computational foundation, timing representation/hardware model, dataflow, psl, lambda calculus}
As part of this thesis we will introduce and explain the problem domain we are working in. 
In this chapter the following items will be discussed:
\begin{itemize}
 \item Hardwarematic \& Softwarematic Computation
 \item Models of Hardware\todo{only sanders/lee?}
 \item Time Representation 
\end{itemize}

\subsection{Total and Partial functions}
In order to combine the two different concepts of stateful and non-stateful functions we first need to define a computational foundation to express the composition of these two different concepts.
To create a robust framework where we can combine different computations we first need to define the concepts we will be using.
First we will define what a function is, what a partial function is and how these relate to hardware representations.

\begin{figure}[H]
A \textbf{(total) function} is a binary relation $f_t \subseteq A \times B$ such that:
\[ \forall a \in A. \forall (b1,b2) \in B.( f_t(a) = b1 \land f_t(a) = b2 \Rightarrow b1 = b2) \]
for which $ \forall a \in A. \exists b \in B. ( f_t(a) = b ) $ holds.
\end{figure}

\begin{figure}[H]
A \textbf{partial function} is a binary relation $f_p \subseteq A \times B$ such that
\[ \forall a \in A. \forall (b1,b2) \in B.( f_p(a) = b1 \land f_p(a) = b2 \Rightarrow b1 = b2) \]
and for which $ \forall a \in A. \exists b \in B. ( f_p(a) = b ) $ does not have to hold.
\end{figure}

\todo[inline]{Merge this with timing talked about later}
Partial functions by itself are too abstract to reason about physical computing machines, as we have not defined yet what it means for a function to be undefined.
When using physical machines to execute computations we are only interested in certain sets of inputs which lead to certain sets of outputs.
Consider a hardware component\footnote{Whether this is a complete piece of hardware or merely a subcomponent does not matter in this case.} with a singular input and singular output.
This hardware component is defined for every continuous input and continuous output; it is a reactive system.
Since we only define synchronous systems, we are not interested in the entirety of inputs and outputs but only in the inputs and outputs as they are at synchronized steps.
To express this we can use a \textit{timed model} as introduced by \citeauthor{lee1998framework}\cite{lee1998framework}.
There a tagged signal model is introduced, which we will repeat here for convenience.

\begin{figure}[H]
An \textbf{event} $e$ is a member of the set $T \times V$, where $T$ are tags and $V$ are values associated with this tag.
\end{figure}

\begin{figure}[H]
A \textbf{signal} $s$ is a set of events such that it is a member of the \textit{powerset} $\mathcal{P}(T \times V)$.
The entire set of signals is named $S$, and is defined as $S = \mathcal{P}(T \times V)$.
\end{figure}

They then define a \textit{functional signal} as a (possibly) partial function $f_p : T \rightarrow V$, as well as a tuple \textbf{s} which is formed by $N$ signals and denoted $S^N$.
Furthermore, they define the empty signal as $\lambda$, the tuple of empty signals as $\Lambda$ and define union of the empty signal as follows:
\[ s \cup \lambda = s \]
This is not useful in our case however. 
Take for instance a partial function $f_p : S^N \rightarrow S^M$ representing a certain hardware component which uses $N$ input signals to generate $M$ output signals.
When we supply one of the inputs with a empty signal then the result, which is part of the tuple $S^M$ is at least partly empty as well. 
We defend this notion by claiming that if an empty signal does not affect the result of a computation then the input may be discarded in its entirety.
Therefor we can define for any signal s:

\[
\begin{aligned}
    s \cup \phi &= \phi \\
    s \cup \Phi &= \Phi
\end{aligned}
\]
, with $\lambda = \phi$ and $\Lambda = \Phi$ to avoid confusion when discussing the lambda calculus and related concepts.

The reasoning behind this different definition may not seem clear right away, but for our purpose of hardware description we need to have a clear definition of what is a \textit{valid} computation.
To give form to this definition we need to define a undefined value.
In certain models a undefined value is indicated by the absence of a value, which is often represented by $\bot$.
In our model, $(t,\bot) \in \phi$, for any $t \in T$.
Furthermore, if any event $e \in S^N$ is $\bot$, then $S^N \in \Phi$.\todo{Add predicate logic}.
This means that, if there is an undefined value at any point of a signal $s$, either for a component input or output, the entire component is undefined for this \textit{specific} n-tuple of signals.

Due to the union operation as described earlier this means $\bot$ propagates. 
In our system we do no allow $\bot$ values, as we need to be certain that for every input the output is defined.
Sometimes however we want to define an actual absence of value.
The programmer should be able to define $V$ as:
\[ 
V = 
\begin{cases}
    V'\\
    \hat{\bot}
\end{cases}
\]
, where $V'$ are actual values and $\hat{\bot}$ represents an intended absence of value.

Later in this chapter we will define various forms of composition, but first we use the timed model as presented by \citeauthor{lee1998framework} to limit our partial functions to only include synchronous moments.
In their paper, they assume time is \textit{uniform} (i.e. ignoring relativistic effects).
Here we will also assume time is discrete, since reasoning about synchronous system is easier in that regard.
Furthermore, as we are modelling a system wherein time is uniform and discrete, we do not allow crossing clock domains if different clocks have different clock sources, since this would violate the absence of relativistic effects.\todo{If we later do support crossing clock domains it should be mentioned here as well}
The timed model they present imposes an \textit{ordering relation} on the set of tags $T$, turning $T$ into a \textit{totally ordered set}.
That is, for any distinct $(t,t') \in T$, $t < t'$ or $t' < t$.

As shown here, we can combine the idiomatic style of a functional language, a basic mapping between inputs and outputs, with physical machines if we drop the restriction that for every input there must be a certain output.
For certain inputs the computation may be undefined. 
Following in chapter/section x, we will show that we can detect these undefined computations when applying a (possibly partial) function to a signal. \todo{Needs reference to where we 'prove' this?}
Later on we will present an elegant way to define these partial functions as well introducing the concept of \textit{time variables} which allow us to exactly define for which sets of signals $S' \in S$ the circuit has correct behaviour.

\subsection{Streaming Systems}
\todo[inline]{This is out of place/needs to be rewritten}
Of course, streaming languages might have a better, or a more consistent solution. 
Given a stream \[\vec x = (x_1,x_2,\ldots,x_n)\], we can define a function whose argument is a function, a initial value for the memory elements and a stream of values.
The function combines both an intermediate result, which is based on all the previous results from the stream, together with new value, to produce an output and a new memory element.
This behaviour can be captured by |scanl|:

%\begin{texexptitled}[text only,float]{Stateful function definition}{code:stateful}
%\begin{code}
%scanl :: (a -> b -> a) -> a -> vecb -> veca
%scanl f init xs = ...
%\end{code}.
%\caption{|scanl| in streaming languages}
%\end{source}
%To define a continuous sum we can take this function and apply it as follows, with 0 being the initial memory value:
%\begin{source}
%\begin{texexptitled}[text only,float]{Stateful function definition}{code:stateful}
%\begin{code}
%sum :: veca -> veca
%sum = scanl (+) 0
%\end{code}.
%\caption{|sum| in streaming languages}
%\end{source}
%But still, this introduces some noise in the function body if we want delays, for instance to represent simply fifo buffers:
%\begin{source}
%\begin{texexptitled}[text only,float]{Stateful function definition}{code:stateful}
%\begin{code}
%fifo :: Int -> veca -> veca
%fifo x = delayx EOL
%\end{code}
%\caption{|fifo| in streaming languages}
%\end{source}
%whereas the actual operation is the identity function.
%In essence, the function body is no longer about what we want to \textit{do}, but about managing spatial information.

\section{Timing representation}
Aside from the level of abstraction, there are also timing representations to consider. 
For hardware, timing is very important. 
If we view time as continuous, then we can see hardware as a reactive system which continuously reacts to stimuli on the smallest level.
Whenever a certain computation is made in a physical system it will take a certain amount of time for the results of this computation to become stable.
When composing multiple systems or processes then each process will need its inputs stable, leading to a certain delay to start this process. 
What is important to realize is that the resulting implementation has certain timing constraints, but the model on which the physical implementation is based might have an implicit or an explicit notion of time, depending on the criteria of the designer.
\cite{jantsch2005models} and \cite{chang1997heterogeneous} give an excellent overview of the different timing models used within hardware design.
Out of these models we will focus on the synchronous and discrete timing models, since these are the areas that naturally fit in the context of \gls{clash} and this thesis.
We will discuss the following models:
\begin{itemize}
 \item Discrete event models
 \item Synchronous models
 \item Dataflow models
\end{itemize}

These three different timing models have different properties and come more natural to describe certain problems, but will not be suited for all different problem types. 
Within discrete event models entities react to events which occur at a specific time instance and which may only produce values at the same time instance or at a later time instance. 
Execution is chronological in the sense that earlier events are executed before later events.
According to \cite{chang1997heterogeneous}, time is an integral part of the discrete event model, which brings the definitions of discrete event models and discrete time models as mentioned by \cite{jantsch2005models} together.

Discrete event models then describe time by natural numbers where each different moment in time is assigned a value. 
A certain value is valid at a certain point in time, or phrased differently: each event, namely the production of a value, has specific timing information added to it, which gives the total sequence of events a natural ordering. 
Discrete-time models are used in simulation of both \gls{vhdl} and Verilog. 
Within this model combinational logic can both be described as having zero delay, which is easier conceptually, or having a certain non-zero delay which conforms more to a physical circuit. 
The latter is often used for synthesis, where clockspeed of an entire circuit can be derived from the critical path in said circuit. 

Abstracting away from this concept gives synchronous\footnote{Note that synchronous in this context is meant as ``computation having zero delay, not synchronous as in a clocked circuit.''} models, where the moments in time do not denote physical units in time, but represent abstract moment in time. 
Due to this abstraction it is easier for the designer to focus on functionality, as he only needs to make sure the correct values are synchronized as opposed to making sure the values are available at the same time and long enough for the computation to be done.
According to \cite{jantsch2005models} this leads to a clean separation between communication and computation, as each computation is instantaneous and the entire clockcycle is used for communication between processes. 
The assumption that computation is instantaneous is called the \tif{synchrony hypothesis}.
Aside from a clean separation between communication and computation the sychronous model offers easy composition.
In a synchronous model, components can be decomposed and composed without having any real influence on the model used, as mentioned by \cite{benveniste1991synchronous}.
When composing components the actual delay, in the physical sense, that occurs is increased, though in the model itself the entire component still takes one cycle. 
This makes developing hardware possible without dealing with an explicit notion of time.
If cyclic dependencies are allowed in the synchronous language then according to \cite{chang1997heterogeneous} execution of the language involves finding a \textit{fixed point}, or a consistent value for all events at a given time instant.

Dataflow languages have no concept of time, since they only define what should happen given enough tokens are available as inputs.
Communication then takes place in \textit{streams} of values, each containing a various number of tokens.
A data flow language is a language that describes a system in terms of data dependencies between processes. 
\cite{ackerman1982data} mentions there are several properties to keep in mind when discussing data flow, of which I will cite the relevant ones to hardware description:
\begin{itemize}
 \item 
    ``Freedom from side effects.''
    This is a property that works extremely well with functional languages.
    Pure functions are inherently side effect free, so modelling processes as having no side effects is natural to functional languages.
 \item
    ``Locality of effect.''
    Similarly to the previous property, this one works well with functional languages for the same reasons.
 \item 
    ``A "single assignment" convention.''
    Variables can be seen as labeled wires within a hardware design. 
    If viewed as such then the single assignment convention not only makes sense, but should be enforced to not have multiple drivers of a signal.
 \item 
    ``A somewhat unusual notation for iterations, necessitated by freedom from side effects and single assignment.''
    This property does not really work well with functional languages, but highlights a major `shortcoming' of functional languages. Iterations have to be done using recursion, which cannot easily be translated to hardware. This issue will be explored in greater detail later.
 \item
    ``A lack of `history sensitivity' in procedures.'' 
    As the authors already mention, this is not really true in all cases, and this is especially not the case for hardware designs.
\end{itemize}

There are many different languages and models in use today to express dataflow.
One of the commonly used models is SDF\cite{lee1987synchronous}, which allows \textit{static scheduling}, a property which important for being able to construct a schedule from static information.
There are also a various number of languages that are based of the same synchronous principle, such as Lustre\cite{halbwachs1991synchronous}, Signal\cite{amagbegnon1995implementation} and many others.
