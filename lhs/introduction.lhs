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

\chapter{Introduction}
Hardware description languages are used to describe digital logic and electronic circuits.
Time is a primary attribute of hardware, and as such \glspl{hdl} such as \gls{vhdl}\cite{navabi1997vhdl} and Verilog\cite{thomas2002verilog} have the ability to express behaviour as a function of time.
Even though \gls{vhdl} and Verilog have the ability to specify behaviour as a function of time, they do \textit{not} have the ability to verify the correctness of specifications which include time-dependent behaviour.
Verification of \gls{vhdl} code which introduces time-dependent behaviour is done manually via simulation.
After specification of functionality, the specification is simulated in order to test whether or not the resulting hardware representation behaves as intended by the designer.
Even though verification through simulation can be automated by languages such as \gls{psl}\cite{eisner2006practical}, verification still solely depends on the input from the designer.

Functional programming languages such as Haskell\cite{jones2003haskell}, ML\cite{milner1978theory} and many others, have traditionally been used in areas where verification is important.
The functional paradigm uses side-effect free functions, i.e. the result of a function only depends on the argument(s) of the function.
These functions are called ``pure'' functions. 
Such functions can be represented using a formal system called the $\lambda$-calculus.
In pure functions, results may only depend on the argument of a function, without modifying the arguments in the process. 
Compositions of pure functions are easier to reason about as a result, as functions do not affect each other aside from through their direct argument(s) and result(s).
In functional languages, the type system is used to reason about the effects of function application and abstraction.
The type system provides the proof that certain expressions are indeed well-typed, or conversely, provide the proof that certain expressions are not well-typed.
Expressions which are not well-typed are rejected by the compiler, as correct behaviour cannot be guaranteed.

Functional \glspl{hdl} such as \glslink{clash}{C$\lambda$aSH}\cite{clashchris,kooijman2009haskell}, the \gls{forsyde}\cite{sander2004system} language and Lava\cite{bjesse1998lava} can transform a description in the form of a functional language to hardware, often by first transforming the functional specification to \gls{vhdl}.
The translation to \gls{vhdl} is made in order to create actual hardware, by using the synthesis tools that already exist for \gls{vhdl}.
Although creation of hardware directly from functional descriptions is possible, the implementation costs are high enough to warrant usage of an intermediate language such as \gls{vhdl}.
Unlike traditional \glspl{hdl}, functions are considered values in functional \glspl{hdl}.
Even though functions do not have straightforward bit-representations, first-class functions are certainly useful in the domain of hardware description, as demonstrated by \gls{clash}, \gls{forsyde} and Lava.
As functions are values, the type system used in \gls{clash} and other functional \glspl{hdl} also defines the types of functions.
Since the types of functions and the type of data used by functions is known at compile-time, guarantees can be given about the correctness of expressions in these languages.
The type system of \gls{clash} allows polymorphism and higher-order functions, which enables increased code-reuse and greater conciseness than traditional \glspl{hdl}.

The most common method to reason about time-dependent behaviour in hardware design is through synchronous hardware design.
Synchronous hardware uses two elements, namely memory elements and combinational logic.
The memory elements in a circuit are updated in synchrony according to a clock, making its behaviour time-dependent.
This contrasts with combinational logic, which has time-independent behaviour.
The synchronous approach makes it possible to more easily reason about concurrency, as time-dependent behaviour is limited to certain time-frames, called clock cycles.  
Nevertheless, current mainstream \glspl{hdl} do not support verification of compositions of components which have time-dependent behaviour.
Synchronous languages, such as Lustre\cite{halbwachs1993tutorial} and Esterel\cite{berry1992esterel}, do support verification of time-dependent compositions.
However, current synchronous languages do not give the developer insight into how this verification is performed, nor explicitly show the time-dependent behaviour of components in a concise manner.
This is different for many functional (hardware description) languages, where the type system is often an integral part of the language.
The type system of Haskell for instance, gives the developer an intuitive interface through which properties of programs are made explicit.
These properties are then used in the verification process, which determines whether the stated properties of programs actually hold.

In this thesis, we aim to extend the existing functional \gls{hdl} \gls{clash} with verification mechanisms similar to those used in synchronous languages.
In short, the question permeating through the pages of this thesis is:\newline
\begin{changemargin}{1cm}{1cm}
\begin{doublespace}
\Large ``How can we express time-dependent behaviour of synchronous hardware through the type system.''  
\end{doublespace}
\end{changemargin}

To do so, we create a type system which, as opposed to existing synchronous languages, allows us to reason about time-dependent behaviour using the $\lambda$-calculus.
As naming would suggest, synchronous languages are especially useful for specifying synchronous hardware designs.
Synchronous hardware design, where memory elements are updated synchronously via a clock, makes it possible to reason about the timing characteristics of hardware components, without needing to take all the physical details (such as the propagation delay) into account.
\gls{clash} already enables the designer to specify such time-dependent behaviour through specification of sequential logic.
Memory elements are updated according to a clock, while combinational logic produces results immediately when provided with input(s).
Even though function application is used in \gls{clash} to compose combinational logic, the same operation cannot be used to compose sequential logic.
To compose pure functions with stateful functions, a formalism in the Haskell language called ``arrows''\cite{hughes2000generalising} is used\cite{gerards2011higher} in \gls{clash}.
The use of arrows requires extensive knowledge of functional programming, which is not very common for hardware designers.
Aside from extending \gls{clash} with verification of time-dependent behaviour, we also introduce an easy to use method to compose sequential logic with combinational logic.

\section{Scope} \label{sec:scope}
To be able to confidently answer the research question posed in the previous section, we set the following objectives for this research:
\begin{enumerate}
 \item  To investigate how time can be represented in the type system from a syntactical point of view.
 \item  To investigate how temporal effects within a single clock domain can be expressed as part of the type system.
 \item  Providing formal semantics of the type system through which type soundness may be proven. 
        Proving type soundness is out of the scope of this thesis however.
 \item  To develop an implementation, which shows the practical feasibility of expressing time as part of the type system.
\end{enumerate}

\section{Thesis Structure}
As part of this thesis a comparison between \gls{clash} and two other languages is conducted, namely Lustre\cite{halbwachs1993tutorial} and \gls{forsyde}\cite{sander2004system}.
As the comparison has no direct relation to the objectives of this thesis, it is added as an appendix.
First, various form of the $\lambda$-calculus are discussed first to provide the necessary background information.
Second, we introduce the syntax of our extension to \gls{clash} through examples, after which we show how the time-dependent behaviour of compositions is inferred by the type system.
After doing so, we introduce typing rules to formalise the relation between types and expressions of the underlying $\lambda$-calculus.
Next, the implementation of a prototype implementation of the type system is discussed. 
This prototype implementation is slightly different from the type system discussed earlier.
Afterwards we discuss the results of our work in the conclusion, before finally ending with a discussion of future work.
Finally, we end this thesis with a conclusion.

