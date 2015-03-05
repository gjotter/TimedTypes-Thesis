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
%format EOL = "."

\chapter{Models of Computation}
As part of this thesis we will introduce and explain the problem domain we are working in. 
In this chapter the following items will be discussed:
\begin{itemize}
 \item Hardwarematic \& Softwarematic Computation
 \item Models of Hardware
 \item Time Representation 
\end{itemize}

The first part will deal with computational models, which model is currently used by \gls{clash} and what extensions could reasonably be made to make \gls{clash} a useable alternative to other \gls{hdl}s. 
This already limits the possible solutions to the problem at hand; each solution needs to be, in principle, combinable with \gls{clash} it its current form.
Not only that, whatever solution we give has to be suitable for a hardware engineer. 
For instance, a deep knowledge of Haskell to design hardware with \gls{clash} should not be needed.
This is mostly due to the fact that, while Haskell is flexible, certain notions such as local state are not easy to implement in purely functional languages.
While we should not want to detract from work already done regarding \gls{clash} it is important to realize there may be solutions to our problems which lie outside of the scope of functional programs.

\section{Hardwarematic \& Softwarematic Computation}
Before looking at solutions for the problem at hand we shall first define what we are trying to do when writing both software programs, as well as hardware programs.
The act of designing and writing software programs is often called Software Engineering, and the act of designing and writing hardware ``programs'' is often called Hardware Engineering. 
Together they form a discipline called Computer Engineering.

The general process in both of these disciplines, especially when the target is constrained to \glspl{fpga} in the case of Hardware Engineering, is much the same. 
What we want to do, in both cases, is  
\begin{inparaenum}[\itshape a\upshape)]
\item indentify the nature of the problem to be solved;
\item create structures that represent \textit{computations} which solve these problems;
\item map the entire composition of these computations to a physical machine capable of executing them.
\end{inparaenum}

In essence the process is the same, even though the two disciplines sometimes deal with vastly different problem types.
The last step is the only step which is slightly different.
When writing software we abstract away from the time it takes to do a computation and assume we will have enough space available for doing our computations.
When writing hardware we do not \textit{want} to abstract away from the time it takes it needs to do a computation, since we need to be sure the sequence of events in a system occur in exactly the order in which we specified them.
Since the essence of a hardware description language is the same as a software language, albeit more restricted, we should be able to combine the two when we can restrict the software programs to a certain formalized restricted model.
In the next subsection we will look at the computational nature of both hardware description languages and software languages and identify the fundamental differences between these languages.

\subsection{Computations in Hardware}
\todo[inline]{Add little bit of info on how functions can be seen as components}.
In the context of hardware we do not have a representation for a partially applied function directly, i.e. a partially applied function cannot be transmitted over a wire, but a partial \textit{computation} is a construct we can relate to hardware components.
A hardware component simply represents a computation which, when applied to a sufficent number of parameters will be able to form the result as described in the body of the computation.

Using computations we can easily reason about components in our designs without classifying them and focus on other problems when dealing with larger designs, such as composability.
If we see hardware as a simply another target architecture with a number of interesting properties and try to map computations to the architecture we can see that the basic operation used is \textit{splitting} of big computations in \textit{individual} and \textit{independent} computational units.
A functional language expresses this well, especially since type checking ensures a certain degree correctness of the interfaces between these computational units.

\subsection{Universal Turing Machines \& Well-defined Computations}
\todo[inline]{This entire section is a bit... too complex, too abstract? I do feel like we're combining a restricted form of computation with a non-restricted form of computation, so this stuff \textit{does} matter in my opinion. But should it be mentioned in the thesis at all?}
When we look at languages which are used to describe software we can note a few things: 
\begin{inparaenum}[\itshape a\upshape)]
 \item they use various paradigms to \textit{organize} computations;
 \item they are \gls{turingcomplete} and as such there is always a transformation between any two languages which are \gls{turingcomplete}.
\end{inparaenum}
However, in terms of hardware this notion of Turing completeness is too general to be useable, since we are constrained to certain resources.  
\citeauthor{copeland1999beyond} explore this and introduce the concept of resource-relative computations. 
Furthermore, they state that, given a network of \gls{turingcomplete} machines, we may only reduce these networks to a single Turing machine if all of the Turing machines work in synchrony.
If we consider that the computations which can be executed by Linear-Bounded Automata \todo{Definitely needs more work, and references} are a strict subset of the set of computations which can be executed by a Turing machine, then we may also assume that a \gls{turingcomplete} language can express these computations.
With this knowledge we can also determine that \textit{networks} of Linear-Bounded Automata can be reduced to a single specification in a \gls{turingcomplete} language.
Moreover, if we can restrict every Linear-Bounded Automata to operate in synchroncy, then we can also say that the composition of Linear-Bounded Automata can be described using a language that is accepted by a single Linear-Bounded Automata.\todo{Ho ho ho, wat een aanname}

In short, if we can define a restriction of on \gls{turingcomplete} language which makes the restricted \gls{turingcomplete} language executable on physical machines, then we can combine this with parts which are bounded by resource limits.

%
% Hardware Models
%
\section{Models of Hardware} \label{ch:moh}
Within this chapter we will discuss four relevant topics regarding hardware models, namely:
\begin{itemize}
 \item Classification of Systems
 \item Structural \& Behavioral Descriptions
\end{itemize}

\subsection{Classification of systems}
To reason about the models of hardware we first need to classify the different aspects of hardware systems, so we can create a model which works for all aspects within a functional language.
Within hardware one can easily identify combinational systems and sequential logic, but can we match this with existing system classifications used in formal languages?

As \cite{harel1985development} points out there are multiple dichotomies one can identify when talking about types of systems.
Within general purpose programming there is a difference between specifying a parallel or concurrent program and a purely sequential program.
For \glspl{hdl} this is not very relevant in its entirety. 
Concurrent programs have non-deterministic control flow, since the ordering of communication between entities does not have to be fixed.
This might be relevant to a certain class of problems, but due to its non-deterministic nature it would be harder to reduce this model to something that will run on actual hardware.
Parallel languages, such as the promising Cilk\cite{blumofe1995cilk} language, force the control flow to be deterministic, something which is much more suited for systems that need to be represented with hardware.

\subsection{Reactive \& Transformational Systems}
The dichotomy \cite{harel1985development} mentions is the distinction between reactive systems and transformational systems.
A transformational system is described as a black box. 
A pure transformational system depends on specific input from the outside world, but is not defined for all inputs from the outside world.
Even though this is not a very realistic system it shows how pure functional languages can be used well for describing systems like it.
This matches well with combinational logic in hardware, as long as the combinational logic is not exposed directly from the outside of a black box. 
When all inputs are known combinational logic can be used to implement the transformations on data. 
This means that, in order to be a pure transformational system, there may be no state involved in the system. 
This is again something which suits a functional language. 

A reactive system is, like the name suggests, continuously reacting to stimuli from the outside world. 
This is very different from transformational systems which simply do a one-to-one mapping between input and output.
As \cite{harel1985development} mentions these reactive systems do not lend themselves to be described in terms of functions and transformations, though they do mention the possibility to add time as an additional input to transform the reactive system into a transformational.

So how can we describe reactive systems and transformational systems?
We can already define transformational systems quite well. 
Transformational systems can generally be easily decomposed into different functions, with the entire program describing the structure of the transformation. 
Code snippet \ref{code:transformational} should make it clear how a system which transforms a number by first adding 1 to it, and then adding 2 to it can be modelled in a functional language:
\begin{source}
\begin{code}
trans = (+1)

trans' = (+2)

system = trans' . trans
\end{code}
\caption{Composing functions into a single transformational system} \label{code:transformational}
\end{source}

For reactive systems this is not so straightforward.
In principle these systems can be easily described using finite state machines, but as these systems grow in complexity the number of states can grow exponentially.
Composition and decomposition are also not easy to do using finite state machines.
But this gives rise to the question, do we even want to define reactive systems?
If we assume the synchrony hypothesis \todo{needs reference}, then we should not even care about reactive systems, as there is no notion of \textit{continuously} reacting to stimuli.
Therefor, the distinction between reactive systems and transformational systems is moot, and we should be able to express our hardware constructs using only transformational systems.
Later, in chapter \todo{needs chapter ref}, we will return to this distinction, but for now we can put this dichotomy aside.

\subsection{Streaming Systems}
\todo[inline]{This is out of place/needs to be rewritten}
Of course, streaming languages might have a better, or a more consistent solution. 
Given a stream \[\vec x = (x_1,x_2,\ldots,x_n)\], we can define a function whose argument is a function, a initial value for the memory elements and a stream of values.
The function combines both an intermediate result, which is based on all the previous results from the stream, together with new value, to produce an output and a new memory element.
This behaviour can be captured by |scanl|:

\begin{source}
\begin{code}
scanl :: (a -> b -> a) -> a -> vecb -> veca
scanl f init xs = ...
\end{code}.
\caption{|scanl| in streaming languages}
\end{source}
To define a continuous sum we can take this function and apply it as follows, with 0 being the initial memory value:
\begin{source}
\begin{code}
sum :: veca -> veca
sum = scanl (+) 0
\end{code}.
\caption{|sum| in streaming languages}
\end{source}
But still, this introduces some noise in the function body if we want delays, for instance to represent simply fifo buffers:
\begin{source}
\begin{code}
fifo :: Int -> veca -> veca
fifo x = delayx EOL
\end{code}
\caption{|fifo| in streaming languages}
\end{source}
whereas the actual operation is the identity function.
In essence, the function body is no longer about what we want to \textit{do}, but about managing spatial information.

\subsection{Structural \& Behavioral Systems}
One of the more fundamental topics is how to deal with simulating and reasoning about hardware.\todo{Rewrite+ more content}
What models are useful and accurate when compared to their physical implementations. 
There is a certain tradeoff which can be made here. 
When designing a system in a \tif{structural} way the model is based around a one-to-one correspondence between model and implementation.
This can lead to highly efficient and highly specified systems. 
Unfortunately this can also lead to a high investment in time as \cite{camposano1989synthesizing} mentions. 
In more \textit{behavioural}\footnote{Note that we are talking about the behaviour of a circuit here which has a implementation in hardware, not the behavioural description used in existing HDLs like VHDL. \cite{claessen2002embedded} uses the term ``synthesisable behavioural description'' for this.}  approaches this investment in time is lessened, since the designer only has to define the functionality which is intended; how the system needs to behave. 
It can therefor be said that behavioural descriptions are more abstract than structural descriptions and might have multiple implementations.

The question is however, why use such a restriction in the language when both could be united in one approach? 
Ideally when designing a system the designer will first lay down the general principles and behaviour of the system without concerning with the details.
As more information is gathered about the system, specific information may be added to further refine the system, leading to an efficient implementation. 
Rapid prototyping can be used to construct the initial system(s) and used to do further refinement.
A combination of both has been investigated in \cite{claessen2002embedded}, using the Lava framework\cite{bjesse1998lava}. 

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
