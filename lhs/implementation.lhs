%include polycode.fmt 
%format |-> = "\mapsto"
%format veca = "\vec a"
%format vecb = "\vec b"
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
%format .>= = ".\geq"

\tikzstyle{materia}=[draw, fill=gray!20, text width=6.0em, text centered,
  minimum height=1.5em,drop shadow]
\tikzstyle{blocktitle} = [materia, text width=15em, minimum width=15em,
  minimum height=3em, rounded corners, drop shadow]
\tikzstyle{texto} = [above, text width=15em, text centered]
\tikzstyle{linepart} = [draw, thick, color=black!50, -latex', dashed]
\tikzstyle{line} = [draw, thick, color=black!50, -latex']
\tikzstyle{ur}=[draw, text centered, minimum height=0.01em]
 
% Define distances for bordering
\newcommand{\blockdist}{1.3}
\newcommand{\edgedist}{1.5}

\newcommand{\blocktitle}[3]{node (p#1) [blocktitle]
  {#2 \\{\scriptsize\textit{#3}}}}

% Draw background
%\newcommand{\background}[5]{%
%  \begin{pgfonlayer}{background}
%    % Left-top corner of the background rectangle
%    \path (#1.west |- #2.north)+(-0.5,0.5) node (a1) {};
%    % Right-bottom corner of the background rectanle
%    \path (#3.east |- #4.south)+(+0.5,-0.25) node (a2) {};
%    % Draw the background
%    \path[fill=yellow!20,rounded corners, draw=black!50, dashed]
%      (a1) rectangle (a2);
%    \path (a1.east |- a1.south)+(0.8,-0.3) node (u1)[texto]
%      {\scriptsize\textit{Unidad #5}};
%  \end{pgfonlayer}}

\newcommand{\transreceptor}[3]{%
  \path [linepart] (#1.east) -- node [above]
    {\scriptsize Transreceptor #2} (#3);}

\chapter{Implementation}
In this chapter, we discuss the implementation of the prototype typechecker.
The prototype checker was originally made to explore the feasibility of expressing time as part of the type system.
As such, not every feature of the discussed type system is implemented here.
Moreover, the implementation is different from the type system presented in the previous chapter in a number of ways.
We discuss the difference at the end of this chapter.

The prototype is made using the Haskell language. 
As such, knowledge of Haskell is required to interpret the code examples.
Not all the code is shown however.
In this chapter we discuss the implementation, but do not provide a full coverage of all source code used to create it.
If needed, code examples are provided and explained.

To discuss the implementation, we first provide a general overview on how the typechecker is implemented.
Secondly, we introduce the relevant parts of the grammar used by the typechecker.
Finally, we introduce the modified unification algorithm and the method we use to derive and verify timing constraints from expressions. 

\section{Introduction}
Before going into details, we first provide a general overview on how we created the typechecker.
In our typechecker, we support both base types, such as |Bool| and |Int|, as well as time expressions.
In the implementation these are separated before unification, as shown by figure \ref{fig:overview}.
As mentioned in earlier chapters, we use constraint-based typechecking.
Constraint-based typechecking makes it possible to \textit{infer} the type of a term, at least if it has a valid type.
The algorithm we use is a modified version of the algorithm discussed in ``Types and Programming Languages''\cite{pierce2002types}, and as such does not behave exactly the same as the type system presented in chapter \ref{ch:typesystem}.
A single constraint generation algorithm is used to generate both the constraints of base types, as well as the constraints for time expressions.
As such, we can infer the time-dependent behaviour from terms.
The unification algorithm is slightly different for time expressions and base types however, which is why the implementation of these two are separated.

\begin{figure}[H]
\begin{tikzpicture}[scale=0.95,transform shape]

  \path \blocktitle{1}{Parser}{};
  \path (p1.south)+(0.0,-1.5)   \blocktitle{2}{Constraint generation}{Given a term, generate a list of constraints which need to hold for the term to have a type};
  \path (p2.south)+(0.0,-1.5)   \blocktitle{3}{Split}{Splitting base types from time information};
  \path (p3.south)+(-3.5,-1.8)  \blocktitle{4}{Unification}{Unifies the constraints of base types, resulting in a mapping of type variables to types.};
  \path (p3.south)+(3.5,-1.8)   \blocktitle{5}{Unification}{Unifies the constraints of timing information, resulting in a mapping of type variables to concrete time information and time constraints};
  \path (p5.south)+(0,-1.5)     \blocktitle{6}{Timechecking}{Verifies the timing constraints};
  \path (p6.south)+(-3.5,-2.0)  \blocktitle{7}{Merge}{Merges timing information with base types, possibly indicating errors if there is a mismatch};
  \path [line] (p1.south) -- node [above] {} (p2) ;
  \path [line] (p2.south) -- node [above] {} (p3) ;
  \path [line] (p3.south) -- +(0.0,-0.5) -- +(-3.5,-0.5)
    -- node [above, midway] {} (p4);
  \path [line] (p3.south) -- +(0.0,-0.5) -- +(3.5,-0.5)
    -- node [above, midway] {} (p5);
  \path [line] (p5.south) -- node [above] {} (p6) ;
  \path [line] (p6.south) -- +(0.0,-0.5) -- +(-3.5,-0.5)
    -- node [above, midway] {} (p7);
 \path [line] (p4.south) -- +(0.0,-2.75) -- +(+3.5,-2.75)
    -- node [above, midway] {} (p7);
\end{tikzpicture}
\caption{Overview of the implementation of the typechecker.} \label{fig:overview}
\end{figure}

As seen above, the entire typechecking part is split in two parts.
Validation and inference of time expressions is independent from regular typechecking.
This approach has some advantages:
\begin{itemize}
\item Regular typechecking can be used on the base types, something which is well understood already.
\item When merging the results from type and timechecking we can verify that the results from timechecking have the same structure as the ones from typechecking.
      This provides a simple error detection method, increasing the confidence in correctness.
\item If the timechecking algorithm is independent of typechecking the same approach may be used to augment other typecheckers with time information.
\item Extending the timechecking part is easier.
\end{itemize}

Before going into details on how these parts of the typechecker are implemented, we first discuss the implemented grammar the typechecker uses.

\section{The Grammar}
In our implementation we do not parse any source code.
As such, it is easier to use DeBruijn indexing instead of named variables.
If we were to use named variables, we would have to first check which variable belongs to what binder.
When using DeBruijn indices we immediately know which variable refers to which binder.
As an added bonus, we also do not need to concern ourselves with shadowing.

DeBruijn indices are integers which refer to binders.
For instance, the code
\begin{changemargin}{1cm}{0cm}
\begin{expansionno}{text only}
$\lambda x.\lambda y. x \: y$
\end{expansionno}
\end{changemargin}
would become
\begin{changemargin}{1cm}{0cm}
\begin{expansionno}{text only}
$\lambda. \lambda. 1 \: 0$
\end{expansionno}
\end{changemargin}

When using DeBruijn indices, variables are no longer named. 
Instead, variables are numbered.
As shown, the DeBruijn index indicates how many binders need to be skipped to find the binder which the variable belongs to.
To represent functions, the three terms of the $\lambda$-calculus are represented in the grammar as indicated by code snippet \ref{code:term1}.  
The grammar is represented in the language Haskell using \glspl{adt}.
\glspl{adt} allow us to define the grammar concisely. 

\begin{texexptitled}[text only]{Implementation of Term (1)}{code:term1}
\begin{code}
type DeBruijn = Int

data Term   =   TmVar DeBruijn      -- Variable
            |   TmAbs String Term   -- Abstraction 
            |   TmApp Term Term     -- Application 
\end{code}
\end{texexptitled}

We define a |Term| as consisting of either a \textit{variable} (indicated by the type constructor |TmVar|), \textit{abstraction} (indicated by |TmAbs|), and \textit{application} (indicated by |TmApp|).
Using these terms we build expressions of the $\lambda$-calculus.
For instance, term $\lambda x.\lambda y.x \: y$ is represented by the algebraic datatype above as follows:
\begin{changemargin}{1cm}{0cm}
\begin{expansionno}{text only}
|TmAbs "x" $ TmAbs "y" $ TmApp (TmVar 1) (TmVar 0)|
\end{expansionno}
\end{changemargin}

Strictly speaking, the |String| identifiers are not needed.
For debugging purposes it is often handy to have names to identify individual variables however.
So far, the definition of |Term| is very minimal.
In the next section we extend the definition of our language to include type representation. 

\subsection{Implementation of Types}
As mentioned before, we have separated unification of base types and time expressions.
To increase code reuse, we have defined types as a parametric datatype.
This gives us the ability to use the shared structure of function types, variable types and constants between time expressions and base types.

\begin{texexptitled}[text only]{Implementation of MetaType}{code:metatype}
\begin{code}
data MetaType a   =   Arrow (MetaType a) (MetaType a)
                  |   Var VariableIndex
                  |   Constant a

type VariableIndex = Int
\end{code}
\end{texexptitled}

As shown by code snippet \ref{code:metatype}, types in our typechecker are either function types, represented by the |Arrow| type constructor, type variables or constant.
Type variables are represented by integers and used for type-inference, as shown later.
The type constructor |Constant| refers to all types except type variables or function types.
For instance, the type |Int| is a constant type, as is the time expression |<t+1>|.
The definition of |Metatype| allows us to define types such as |Int<t+1>| and \textit{separate} types into base types and time expressions via a transformation function.

To show how |MetaType| is used, we start by defining a function consisting of base types.
Using the definition of |BaseType| from code snippet \ref{code:primtype}, we represent a function with type |Bool -> Int -> Int| as follows:
\begin{changemargin}{1cm}{0cm}
\begin{expansionno}{text only}
|Arrow (Constant Bool) (Arrow (Constant TyInt) (Constant TyInt))|
\end{expansionno}
\end{changemargin}
The above expression has type |MetaType BaseType|, which indicates that this type only contains base type information.

\begin{texexptitled}[text only]{Implementation of Base Types}{code:primtype}
\begin{code}
data BaseType  =   TyBool 
               |   TyInt
\end{code}
\end{texexptitled}

Similarly, we use the definition of |MetaType| to create functions consisting solely of time expressions.
Before introducing the algebraic datatype of time expressions however, we need to be able to introduce time variables.
For this we extend the definition of |Term| as indicated by code snippet \ref{code:term2}.

\begin{texexptitled}[text only]{Implementation of Term (2)}{code:term2}
\begin{code}
data Term   =   TmVar DeBruijn      -- Variable
            |   TmAbs String Term   -- Abstraction 
            |   TmApp Term Term     -- Application 
            |   TmTAbs String Term  -- Time Abstraction
\end{code}
\end{texexptitled}

Similarly to regular function abstraction, time abstraction introduces a time variable.
For example, given a function with type |Int<t> -> Int<t+1>|, the time variable |t| has to be introduced.
The |TmTAbs| term is used to introduce time variables.
We then use DeBruijn indices to create time expressions, as shown by the definition of |TimeExpr| in code snippet \ref{code:unbound}.
The DeBruijn index refers to the time variable introduced by |TmTAbs|.
Time expressions use both a time variable, as well as an offset.
The offset is added to the time variable. 
Since we only support addition, the addition operation is implictly applied to the offset and the time variable.

\begin{texexptitled}[text only]{Implementation of time expressions}{code:unbound}
\begin{code}
data TimeExpr   =   TimeExpr DeBruijn Offset
                |   TimeLiteral Offset

data TimedType = TimedType BaseType TimeExpr

type Offset = Int 
\end{code}
\end{texexptitled}

However, even though we can introduce time variables using |TmTAbs|, we still cannot ascribe terms with types.
Ascription of terms with types is essential in our type system, as it is the only way in which time-dependent behaviour can be specified.
To introduce ascription, we extend the definition of |Term| for the third (and final) time.

\begin{texexptitled}[text only]{Implementation of Term (3)}{code:term3}
\begin{code}
data Term   =   TmVar DeBruijn        -- Variable
            |   TmAbs String Term     -- Abstraction 
            |   TmApp Term Term       -- Application 
            |   TmTAbs String Term    -- Time Abstraction
            |   TmAs Term TimedType   -- Ascription
\end{code}
\end{texexptitled}

Using time abstraction, ascription and time expressions, we can give types to terms. 
For instance, we can ascribe a function |f| with type |Int<t> -> Int<t> -> Int<t+2>| as 
\begin{changemargin}{1cm}{0cm}
\begin{expansionno}{text only}
\begin{code}
TmTAbs "t"  $ 
  TmAs  f   $
        Arrow  (TimedType TyInt (TimeExpr 0 0))
               (Arrow  (TimedType TyInt (TimeExpr 0 0))
                       (TimedType TyInt (TimeExpr 0 2)))
\end{code}
\end{expansionno}
\end{changemargin}

In this piece of code, we first introduce the time variable |t|, before ascribing the function |f| with a type.
The type, as shown earlier, consists of a time expression and base type, together with the proper DeBruijn indices to make every time expression refer to the same time variable.

Now that we have defined a (minimal) definition of types and terms, we can discuss constraint generation.
The constraint generation defines what constraints a term is subject to in order for the term to have a valid type.
As such, constraint generation expresses the relation between types and terms, although it does not define how the constraints which terms are subject to are verified.

\section{Constraint Generation}
We use the grammar as introduced in the previous section to generate constraints.
We represent a constraint as a relation between two types, as shown by code snippet \ref{code:constraints}.

\begin{texexptitled}[text only]{Constraints}{code:constraints}
\begin{code}
type Constraint a = (MetaType a, MetaType a)
\end{code}
\end{texexptitled}

The generated constraints do not show the ordering of computations; they are equalities.
As an example, consider the delay function 
\begin{changemargin}{1cm}{0cm}
\begin{expansionno}{text only}
>delay :: Int<t> -> Int<t+1>
>delay x = x
\end{expansionno}
\end{changemargin}
Here, |x| has both the type |Int<t>| and |Int<t+1>|.
To determine whether this is valid, we need to be able to distinguish between the |x| which is used as an input, and |x| which is used as an output for the function |delay|.
The code of 
\begin{changemargin}{1cm}{0cm}
\begin{expansionno}{text only}
>delay' :: Int<t+1> -> Int<t>
>delay' x = x
\end{expansionno}
\end{changemargin}
should be invalid, to maintain causality.
Using |delay| leads to the constraint |Int<t> = Int<t+1>|, while using |delay'| leads to the constraint |Int<t+1> = Int<t>|.
In order to consider the first constraint valid, while denying the second constraint, we only allow function definitions in the form of |delay|, meaning only \textit{increasing} the delay is allowed within a function definition.
Even though this may seem like a big restriction, it is done with good reason.
When we restrict ourselves to constraints which represent equalities, we can use the constraint generation as introduced\cite{pierce2002types} by \citeauthor{pierce2002types}.
This does not mean the ordering of constraints is not important.
Later in this chapter, when we discuss the modified unification algorithm, we show how we can derive the ordering of function application based on the (unique) time variables functions use.
Even though we do not need inequalities to reason about constraints such as those described by |delay| and |delay'|, we do need them when inferring the time-dependent behaviour of compositions of time-dependent functions.

\begin{texexptitled}[text only]{Constraint generation of abstraction}{code:constraintabs}
\begin{code}
constraints :: Term -> State TypeState (MetaType BoundedType)
constraints tm = case tm of

    TmAbs str tm ->
        do  nvlam   <- freshTypeVar
            nvtot   <- freshTypeVar
            ctx     <- gets context 
            addTypeVarBinding (str,nvlam)
            ty      <- constraints tm
            modify (\s -> s { context = ctx })
            addTypeConstraints [(nvtot,Arrow nvlam ty)]
            return nvtot
\end{code} 
\end{texexptitled}

The constraint generation algorithm allows us to infer the types of terms.
To do so, we need the ability to create \textit{unique} type variables, which represent the (unknown) types of terms.
For this purpose we use the |State Monad|, which holds the in which terms are used, and additional information to generate unique type variables.
When a new, unique type variable is needed, |freshTypeVar| is used to generate the integer which represents the unique type variable.
As an example, consider the code of snippet \ref{code:constraintabs}.
This code snippet defines a function |constraints|, which generates the type constraints a term is subject to.
A |case|-expression is used to match the type constructor of |Term| and allows us to define specific constraint generation rules for each specific |Term|.

In code snippet \ref{code:constraintabs}, the constraints of the |TmAbs| term are generated.
First, a new type variable is generated, which represents the type of the binder.
Given a term $\lambda x.tm$, |nvlam| represents the type of |x|.
The type of |x| is added to the context by adding the mapping between |x| and |nvlam| through the |addTypeVarBinding| function.
This makes it possible for term variables to use the type of the binder they refer to.

Following the context mapping, a type variable is generated which represents the type of the entire $\lambda x.tm$ expression.
Before adding the constraint however, the constraints |tm| is subject to are generated.
After generating the constraints of |tm| through |constraints tm|, the resulting type |ty| is used to define the constraints the term |TmAbs str tm| is subject to.
For abstraction the constraint is |nvtot = nvlam -> ty|, since the type of $\lambda x.tm$ represents a function which, when applied to an argument with type |nvlam|, will return something with type |ty| of |tm|.

It is important to update the context |ctx| carefully however, as |DeBruijn| indices are also used as indices of the context.
To make sure the binding of the type variable to |str| is only used within |tm|, the context is stored in |ctx| before generating the constraints of |tm|.
After generating the constraints of |tm|, the context is restored.

We similarly generate the constraints for |TmApp|, as shown by code snippet \ref{code:constraintapp}.
\begin{texexptitled}[text only]{Constraint generation of application}{code:constraintapp}
\begin{code}
    TmApp t1 t2 ->
        do  ty2     <- constraints t2
            ty1     <- constraints t1
            nv      <- freshTypeVar
            addTypeConstraints [(ty1,Arrow ty2 nv)]
            return nv
\end{code} 
\end{texexptitled}

In our type system, only functions may be applied to values.
As a result, when generating the constraints of an application like |t1 t2|, the term |t1| must have a function type, which first accepts a value with the type of |t2|.
Without inspecting the exact type of |t1| and |t2|, we do not know what the resulting type of the application is.
For this purpose, a fresh variable named |nv| is created.
The constraint application is subject to is |ty1 = ty2 -> nv|.

Referencing variables is not subject to additional constraints.
Variables are introduced by abstraction, and as such the type of the variables is known through the context.
Code snippet \ref{code:constraintvar} shows how the types of variables are found, by looking at the DeBruijn index and finding the binding to the variable as introduced by abstraction.

\begin{texexptitled}[text only]{Constraint generation of variables}{code:constraintvar}
\begin{code}
    TmVar k -> 
        do  ty      <- deBruijn2Var typeVarBind k
            return ty
\end{code}
\end{texexptitled}

The type variables introduced so far are different from time variables.
Later, in the unification step, all type variables are substituted depending on the type of unification used.
When unifying base types, a mapping is created between type variables and base types.
In the case of time expressions however, type variables are mapped to time expressions.
This means that type variables are used for both unification of base types, as unification of time expressions.
Unlike type variables, time variables are explicitly introduced by time abstraction, as shown by code snippet \ref{code:constrainttabs}.

\begin{texexptitled}[text only]{Constraint generation of time abstraction}{code:constrainttabs}
\begin{code}
    TmTAbs str tm ->
        do  nv      <- freshTimeVar
            addTimeVarBinding (str,nv)
            constraints tm 
\end{code} 
\end{texexptitled}

Time variables are scoped by the |TmTAbs| type constructor, and as such is unique between two different scopes, regardless of the identifier used.
We use integers to represent time variables. 
When a new time variable is generated, the last generated identifier for time variables is used and increased with one.
Since the constraint generation algorithm processes terms in a specific order, we use the identifiers to reconstruct the ordering of function application during unification.
This is important, as we would not be able to distinguish between a step \textit{forward} in time (when comparing two types) and a step \textit{backwards} in time.

As mentioned earlier, ascription is the only method through which terms can be bound to a certain type.
As such, ascription is the only method through which time-dependent behaviour can be introduced.
Using the term |TmAs|, we first generate the constraints of the term which is ascribed with a type, as shown by code snippet \ref{code:constraintas}.
\begin{texexptitled}[text only]{Constraint generation of Ascription}{code:constraintas}
\begin{code}
TmAs tm ty -> 
        do  tytm <- constraints tm
            ty' <- bindType ty
            addTypeConstraints [(tytm,ty')]
            return tytm
\end{code}
\end{texexptitled}

After ascribing a term with a type, we process the provided type |ty| by |bindType|.
We process the type |ty| to replace the DeBruijn index from |ty| with the actual numeric time variable it is bound to.
For instance, given the previously introduced term
\begin{changemargin}{1cm}{0cm}
\begin{expansionno}{text only}
\begin{code}
TmTAbs "t"  $ 
  TmAs  f   $
        Arrow  (TimedType TyInt (TimeExpr 0 0))
               (Arrow  (TimedType TyInt (TimeExpr 0 0))
                       (TimedType TyInt (TimeExpr 0 2)))
\end{code}
\end{expansionno}
\end{changemargin}
, the |TmTAbs| term causes the constraint generation to generate a new time variable.
Suppose the unique time variable which is generated has the value |42|, then the DeBruijn index in |TimeExpr 0 0| is changed to |TimeExpr 42 0|.
After replacing the DeBruijn index in the time expression, we add the type constraints such that the type of |tm| equals the rewritten type expression |ty'|.
This method may seem error-prone.
For the purposes of clarification we do not distinguish between time expressions which use DeBruijn indexing and time expressions which do not.
In the actual prototype however, this distinction is made.
For the remainder of the discussion of the implementation this is not needed however, which is why we chose to use a single representation for time expressions here.

To enable the definition of more then just trivial examples, we also define the term |TmIf|, which represents a multiplexer\footnote{We forgo extending the |Term| datatype for simplicity's sake}.
\begin{texexptitled}[text only]{Constraint generation of Choice}{code:constraintif}
\begin{code}
TmIf t1 t2 t3 ->
        do  ty1 <- constraints t1
            ty2 <- constraints t2
            ty3 <- constraints t3
            ntv <- simpleTimeVar
            let booltype = Constant $ TimedType TyBool (TimeExpr ntv 0)
            addTimeVarBinding ("ifbind",booltype)
            addTypeConstraints [(ty2,ty3)]
            addTypeConstraints [(ty1,booltype)]
            return ty2
\end{code}
\end{texexptitled}
First, the constraints of the predicate is determined, after which the constraints for both branches are determined.
To make sure the predicate is actually a |Bool| type, without restricting the time-dependent behaviour of |t1|, we create a free time variable and use it to create a timed type as |Bool<tfree+0>|.
We then constrain |ty1 = booltype| and |ty2 = ty3|.

\subsection{Example of Constraint Generation}
To show what type of constraints are generated, we present the generation of constraints for a specific function.
We use the functions defined in code snippet \ref{code:constraintgenex1} to derive a set of constraints.
The functions of code snippet \ref{code:constraintgenex1} represent the circuit of figure \ref{fig:compositionsel}.
The constraints generated by the algorithm are used by the unification algorithm, which is explained in the next section.
The unification algorithm also introduces additional registers to make the composition work, using the method of composition as introduced in chapter \ref{ch:specification}.
Although the code definition is fairly trivial, it allows us to show how a specification is verified, and how placement of memory elements is derived.

\begin{texexptitled}[text only]{Functions used in constraint generation.}{code:constraintgenex1}
\begin{code}
delay :: Int<t0> -> Int<t0+3>
delay x = x

sel :: Bool<t1> -> Int<t1> -> Int<t1+1> -> Int<t1+2>
sel p x y = if p then x else y

comp pc xc = sel pc xc (delay xc)
\end{code}
\end{texexptitled}

\begin{figure}[H]
\begin{center}
\centering
\includegraphics[width=0.8\textwidth]{images/compositionsel}
\end{center}
\caption{Composition of |sel| and |delayI| to create |comp|.} \label{fig:compositionsel}
\end{figure}


The code from code snippet \ref{code:constraintgenex1} is represented by the \gls{ast} of code snippet \ref{code:constraintgenex2}.
The term |comp| is passed to the |contraints| function as explained in the previous section.

\begin{texexptitled}[text only]{Example of constraint generation (2).}{code:constraintgenex2}
\begin{code}
delayI =  TmTAbs "t0" $ 
          TmAs  (TmAbs "xd" (TmVar 0)) $ 
                Arrow   (Constant $ TimedType TyInt (TimeExpr 0 0)) 
                        (Constant $ TimedType TyInt (TimeExpr 0 3))

sel =   TmTAbs "t1" $ 
        TmAs  (TmAbs "p" $ TmAbs "x" $ TmAbs "y" $ 
              (TmIf (TmVar 2) (TmVar 1) (TmVar 0)))
              (Arrow  (Constant $ TimedType TyBool (TimeExpr 0 0))
              (Arrow  (Constant $ TimedType TyInt (TimeExpr 0 0))
              (Arrow  (Constant $ TimedType TyInt (TimeExpr 0 1))
                      (Constant $ TimedType TyInt (TimeExpr 0 2)))))

comp =  TmAbs "pc" $ TmAbs "xc" $ 
        TmApp   (TmApp  (TmApp sel (TmVar 1)) 
                        (TmVar 0)) 
                (TmApp delayI (TmVar 0))
\end{code}
\end{texexptitled}

The constraints which are generated by the constraint generation algorithm include many type variables.
We choose to represent type variables by |Xn|, where |n| is the unique identifier for the type variable.
Similarly, we choose to represent the time variables by |tn|.
The constraints generated by the algorithm for |comp| are the following:
\begin{changemargin}{1cm}{0cm}
\begin{expansionno}{text only}
\begin{tabular}{l l}
|X1 = X0 -> X3|   &   |X3 = X2 -> X15| \\
|X7 = Bool<t2>|   &   |X13 = X2 -> X14| \\
|X8 = X0 -> X13|  &   |X8 = Bool<t1+0> -> Int<t1+0>| \\ 
                  &   $\quad\:$ |-> Int<t1+1> -> Int<t1+2>| \\
|X8 = X7 -> X10|  &   |X10 = X9 -> X12| \\
|X5 = X2 -> X6|   &   |X14 = X6 -> X15|\\
|X9 = X11|        &   |X12 = X11 -> X9|\\
|X5 = X4 -> X4|   &   |X5 = Int<t0> -> Int<t0+3>|\\
\end{tabular}
\end{expansionno}
\end{changemargin}

As shown, the ascription introduces the constraints |X8 = Bool<t1+0> -> Int<t1+0> -> Int<t1+1> -> Int<t1+2>| and |X5 = Int<t0> -> Int<t0+3>| for |sel| and |delayI| respectively.
The constraint |X7 = Bool<t2>| is introduced by the |TmIf| rule.
To provide a mapping between type variables and types, we must unify the constraints, which we discuss in the next section.

\section{Unification}
We chose to implement a single unification algorithm, which is flexible enough to allow unification of time expressions, as well as unification of base types.
The similarities between both forms of unification are big enough to warrant a flexible definition.
Moreover, at the point of creating the implementation, the method of checking the time expressions was still in development.
As such, a flexible form of unification helped with development, as it allows us to easily modify the unification algorithm.
The unification algorithm is shown by code snippet \ref{code:unification}.
Before applying |unify| to the set of constraints, the constraints are split in a base type part, as well as a part which only contains time expressions.
The unification algorithm only works on constraints which are instances of the |Substitutable| typeclass, shown by code snippet \ref{code:substitutable}.

\begin{texexptitled}[text only]{Substitutable typeclass}{code:substitutable}
\begin{code}
class Eq a => Substitutable z a where
    add     :: Substitution a -> z -> z
    apply   :: ([Substitution a] -> [Substitution a]) -> z -> z 
    match   :: a -> a -> z -> z 
\end{code}
\end{texexptitled}

\begin{texexptitled}[text only]{Unification}{code:unification}
\begin{code}
unify :: (Show a, Substitutable z a) => [Constraint a] -> z -> z
unify [] r = id r
unify (c:cs) r = case c of
    (Constant t1, Constant t2)  -> unify cs $ match t1 t2 r
    (Arrow s1 s2, Arrow t1 t2)        -> unify ((s1,t1) : (s2,t2) : cs) r
    (tyS@(Var idS), tyT      ) 
        | tyS == tyT                  ->  unify cs r
        | not $ idS `isFVIn` tyT      ->  let   cs'   = (tyS |-> tyT) cs
                                                r'    = add (tyS,tyT) $ apply (tyS |-> tyT) r 
                                          in  unify cs' r'

    (tyS, tyT@(Var idT)      )        -> unify ((tyT,tyS) : cs) r
    (t1,t2                   )        -> error "not unifiable " 
\end{code}
\end{texexptitled}

In the substitutable typeclass, |a| represents the type of constraints, which is either a base type or a time expression.
Depending on the type of constraints, a different record can be used to build the list of substitutions.
The list of substitutions provides a mapping between type variables and constant types.
The different operations of the |Substitutable| typeclass are explained when we discuss the unification algorithm.
However, we point out that these operations, together with the polymorphic container type |z|, allow us to modify the resulting substitutions by the unification algorithm.

As shown, |unify| accepts two arguments.
One is a set of constraints, the other being a record type which is defined by the |Substitutable| typeclass.
To clarify the algorithm, we first focus on how it is implemented for base types, before showing how it is implemented for time expressions.
The base type instance of the |Substitutable| typeclass is defined by code snippet \ref{code:priminstance}.

\begin{texexptitled}[text only]{BaseTypes instance}{code:priminstance}
\begin{code}
type Substitution a = (MetaType a, MetaType a)
data BaseRecord = BaseRecord [Substitution BaseType]

instance Substitutable BaseRecord BaseType where
    add x (BaseRecord xs) = BaseRecord (x:xs)
    apply f (BaseRecord xs) = BaseRecord $ f xs
    match x y tr 
        | x == y = tr
        | otherwise = error "x /= y"
\end{code}
\end{texexptitled}

The |unify| function has five distinct cases of constraints which are handled.
First, the constraint between two constant types are compared.
For this, the |match| function is used, which is part of the |Substitutable| typeclass. 
The functionality of |match| depends on the type of constraints which are unified.
In the case of base types, |match| just checks for equality.
When base types are not equal, an error is raised to indicate that the checked term is not well-typed.

The second case of |unify| handles function constraints, where a function type is constrained by another function type. 
When a function type is constrained by a non-function type, then the term is not well-typed.
If it is constrained by another function type, the individual types which make up the function types are \textit{added} to the existing set of constraints.

The third case of |unify| matches a type variable $X_{idS}$ to an unknown type |tyT|.
If the left hand side of the constraint is equal to the right hand side, then the constraint is discarded and unification continues for the remaining constraints.
If they are not the same, then it is checked whether or not the type variable $X_{idS}$ exists as a free type variable within $tyT$.
Checking for free type variables are important.  
Consider the constraint |X0 = X1 -> X0|, where |X0| is not free in |X1 -> X0|.
This constraint is not well-typed, as we do not support recursion.

If this is not the case, then the variable $X_{idS}$ is replaced by |tyT| in the remaining constraints, as indicated by the |(||->)| function.
Since we have made a substitution in the form of $X_{idS} \mapsto tyT$, we store the substitution.
However, aside from applying the substitution to the remaining constraints, the substitution is also applied to the existing substitutions, which is what the |apply| function does in the case of base types.
The way existing substutions are stored depends on the type of constraints which are being unified.
As a result, the functions |add| and |apply| are part of the |Substitutable| typeclass.
In the case of base types, substitutions are added to the record, while existing substitutions within the record are rewritten according to the new substitution.
The fourth case of |unify| is the same as the third case, only with the right hand side and left hand side switched. 
Finally, the fifth case represents the case when terms are not well-typed.

\begin{texexptitled}[text only]{|TimeExpr| instance of |Substitutable|}{code:timeinstance}
\begin{code}
data TimeRecord = TimeRecord 
                { timeSubs :: [Substitution TimeExpr]
                , timeVars :: [(TimeExpr,TimeExpr)] }

instance Substitutable TimeRecord TimeExpr where
    add x tr = tr { timeSubs = x : (timeSubs tr) }
    apply f tr = tr { timeSubs = f $ timeSubs tr }
    match x y tr = 
      let maysub = matchConstantType (x,y)
      in case maysub of
           Just z -> tr { timeVars = z : (timeVars tr)}
           Nothing -> tr
\end{code}
\end{texexptitled}

The same algorithm is used for time expressions. 
The code of snippet \ref{code:timeinstance} shows the |TimeExpr| instance of |Substitutable|.
The unification algorithm uses |TimeRecord| to store substitutions.
The |timeSubs| stores the substitutions, while |timeVars| is used to verify time expressions.
To create substitutions, first the unification algorithm finds the relations between time expressions which are needed to verify the time-dependent behaviour.
These relations are stored in |timeVars|.
After the time-expressions are verified, the \textit{original} set of constraints is modified.
The resulting constraints are then unified \textit{again}, after which |timeSubs| contains the final substitutions.
Adding the substitutions and applying them to time variables is straightforward.
However, matching time expressions is more complex, as shown by code snippet \ref{code:timematch}.
The result of |matchConstantType| are added to |timeVars|, which is used to verify the time expressions.

\begin{texexptitled}[text only]{Matching function for time expressions}{code:timematch}
\begin{code}
matchConstantType c =
  case c of
    (TimeExpr t1 o1,TimeExpr t2 o2)
      | t1 == t2    ->  Nothing
      | otherwise   ->  Just (TimeExpr t1 o1,TimeExpr t2 o2)

    (TimeLiteral o1,TimeLiteral o2)
      | o1 == o2    ->  Nothing 
      | otherwise   ->  error "cannot unify literals o1 o2"

    (c1@(TimeExpr t1 o1),c2@(TimeLiteral o2)) 
                    ->  Just (c2,c1)

    (c1@(TimeLiteral o1), c2@(TimeExpr t2 o2))
                    -> matchConstantType c2 c1
\end{code}
\end{texexptitled}

When matching time expressions, four different cases can be distinguished.
Either a time expression is constrained to another time expression, a literal is constrained to another literal, a literal is constrained by a time expression, or vice versa.
The first case filters the time expressions which are needed to verify the time-dependent behaviour.
For instance, when typechecking the function |f x y = y| with type |Bool<t> -> Bool<t+1> -> Bool<t+2>|, the result would be the equality of |Bool<t+1> = Bool<t+2>|.
This equality is created as |y| on the left hand side of the expression has type |Bool<t+1>|, while |y| on the right hand side of the expressions has type |Bool<t+2>|.
Since these time variables are the same, we can determine that this is indeed allowed, as function definitions can only have \textit{increasing} delays.
However, in a constraint with different time variables, such as |Bool<t0+1> = Bool<t1+2>|, we cannot determine if this is actually allowed behaviour.
For the purpose of checking the time constraints at a later point, the constraint is recorded and added to |timeVars|, as shown by code snippet \ref{code:timeinstance}.

The second case of |matchConstantType| checks literals. 
In the prototype typechecker, these literals are only compared for equality.
For the purpose of showing that the principle of checking time expressions actually work this is enough, though it could be extended to allow delays on values which exist at a specific time.

The last two cases of |matchConstantType| check time expressions which are constrained to literals, and vice versa.
When time expressions are constrained to literals, the constraint is added with the left hand side containing the literal, and the right hand side containing the time expression.

\subsection{Example of Unification}
Given the constraints generated earlier, repeated below for convenience, we unify them.
We only show the full unification of base types here.
To show unification of time expressions, we first need to generate the time variables which are checked seperately.

\begin{changemargin}{1cm}{0cm}
\begin{expansionno}{text only}
\begin{tabular}{l l}
|X1 = X0 -> X3|   &   |X3 = X2 -> X15| \\
|X7 = Bool<t2>|   &   |X13 = X2 -> X14| \\
|X8 = X0 -> X13|  &   |X8 = Bool<t1+0> -> Int<t1+0>| \\ 
                  &   $\quad\:$ |-> Int<t1+1> -> Int<t1+2>| \\
|X8 = X7 -> X10|  &   |X10 = X9 -> X12| \\
|X5 = X2 -> X6|   &   |X14 = X6 -> X15|\\
|X9 = X11|        &   |X12 = X11 -> X9|\\
|X5 = X4 -> X4|   &   |X5 = Int<t0> -> Int<t0+10>|\\
\end{tabular}
\end{expansionno}
\end{changemargin}

After splitting these constraints into base types and time expressions, we can pass them to the unification algorithm.
In the case of base types, the resulting mapping is 
\begin{changemargin}{1cm}{0cm}
\begin{expansionno}{text only}
\begin{tabular}{l l}
|X0 = Bool|               & |X1 = Bool -> Int -> Int| \\
|X2 = Int|                & |X3 = Int -> Int|\\
|X4 = Int|                & |X5 = Int -> Int|\\
|X6 = Int|                & |X7 = Bool|\\
|X8 = Bool -> Int -> Int -> Int| & |X9 = Int|\\
|X10 = Int -> Int -> Int| & |X11 = Int|\\
|X12 = Int -> Int|        & |X13 = Int -> Int -> Int|\\ 
|X14 = Int -> Int|        & |X15 = Int|
\end{tabular}
\end{expansionno}
\end{changemargin}
The constraint generation algorithm defined the type of |comp| to be equal to |X1|.
As shown, the resulting type of |comp| is |Bool -> Int -> Int|, which is as expected.
The remainder of the constraints define the types of each intermediate expression which makes up |comp|.
Given these types, we can reason about the types of every (partial) function and other values.

For time variables this is slightly different, as we have not checked whether time expressions are actually correct yet.
However, |timeVars| result in a list of constraints, which are shown below.
\begin{changemargin}{1cm}{0cm}
\begin{expansionno}{text only}
\begin{tabular}{c}
|<t1 + 1> = <t0 + 3>| \\
|<t1>     = <t0>    | \\
|<t2>     = <t1>    | \\
\end{tabular}
\end{expansionno}
\end{changemargin}

These constraints are used to verify the complete time-dependent behaviour of |comp|, and provide placement information for memory elements.
In the next section we will use the constraints listed above.

\section{Checking Time Constraints}
Multiple methods could be used to verify the time-dependent behaviour using the constraints of |timeVars|.
We chose to use first order logic to express the constrained time expressions, and use \gls{smt} solvers to find integer representations for the time variables used in time expressions.
Using the integer representations for time variables we can then rewrite the time expressions of compositions in terms of a single time variable and its offsets. 

We chose to use the Z3\cite{de2008z3} solver, as it is the only \gls{smt} solver which supports unbounded integers.
A complete discussion about \gls{smt} solvers is out of the scope of this thesis.
However, \citeauthor{de2008z3} define \gls{smt} as follows: ``A \gls{smt} problem is a decision problem for logical first order formulas with respect to combinations of background theories such as: arithmetic, bit-vectors, arrays, and uninterpreted functions.``

Since the Z3 solver is not written in Haskell, we use the library |Data.SBV|\cite{sbv} to handle the interfacing with Z3.
|Data.SBV| provides the Haskell language with the |Symbolic| monad, which allows us to create statements in first order logic.
The library then allows us to use the Z3 solver to find integer representations for time variables.
The usage of \gls{smt} solvers in Haskell or other functional languages is not new.
Liquid Types\cite{rondon2008liquid} for instance are used to extend Hindley-Milner type inference using \gls{smt}-solvers.

As an example, we use the constrained time expressions from the previous section to create a statement in first order logic, which is checked by the Z3 solver.
\begin{changemargin}{1cm}{0cm}
\begin{expansionno}{text only}
\begin{tabular}{c}
|<t1 + 1> = <t0 + 3>| \\
|<t1>     = <t0>    | \\
|<t2>     = <t1>    | \\
\end{tabular}
\end{expansionno}
\end{changemargin}

First, the proper ordering is determined.
Since time variables are created in order, we know that the time variable |t1| must occur later than |t0|.
Similarly, |t2| must occur later than |t1|.
Using the constrained time expressions from above, we can then define the following statement using first order logic:
\[
  \begin{array}{l l}
    \exists t0. \exists t1. \exists t2. & t1 + 1 \geq t0 + 3\\
                                        & t1 \geq t0 \\
                                        & t2 \geq t1\\
                                        & t0 \geq 0\\
                                        & t1 \geq 0\\
                                        & t2 \geq 0
  \end{array}
  \]

We create this statement by using the |Data.SBV| library, and ask Z3 to find integer representations for |t0|, |t1| and |t2|.
We do this by using the |Symbolic| monad, as shown by code snippet \ref{code:symbolic}.

\begin{texexptitled}[text only]{Using the |Symbolic| monad to create statements in first order logic.}{code:symbolic}
\begin{code}
representation = 
  do  t1 <- exists "t0"
      t2 <- exists "t1"
      t3 <- exists "t2"
      constrain $ t0      .>= 0 
      constrain $ t1      .>= 0 
      constrain $ t2      .>= 0 
      constrain $ t1 + 1  .>= t0 + 3
      constrain $ t1      .>= t0
      constrain $ t2      .>= t1
      solve []
\end{code}
\end{texexptitled}

Using the definition of |representation|, we use the |sat| function of |Data.SBV| to ask the Z3 solver to find a integer representation of |t0|, |t1| and |t2|.
In our experience, Z3 automatically finds the minimal integer values, though this is not guaranteed.
In the future, Z3 will also support optimization criteria, allowing us to guarantee the minimal integer values for time variables.
If the time expressions are erroneous, the |sat| function will not return integer representations for |t0|, |t1| and |t2|.

In the case of verifying the behaviour of |comp| however, the |sat| function provides the following integer representations:
\begin{changemargin}{1cm}{0cm}
\begin{expansionno}{text only}
|t0 = 0|\\
|t1 = 2|\\
|t2 = 2|\\
\end{expansionno}
\end{changemargin}

When we assume |t=0|, we can rewrite the existing expressions of the original constraints as follows:

\begin{changemargin}{1cm}{0cm}
\begin{expansionno}{text only}
\begin{tabular}{l l}
|X1 = X0 -> X3|   &   |X3 = X2 -> X15| \\
|X7 = Bool<t+2>|   &   |X13 = X2 -> X14| \\
|X8 = X0 -> X13|  &   |X8 = Bool<t+2> -> Int<t+2>| \\ 
                  &   $\quad\:$ |-> Int<t+3> -> Int<t+4>| \\
|X8 = X7 -> X10|  &   |X10 = X9 -> X12| \\
|X5 = X2 -> X6|   &   |X14 = X6 -> X15|\\
|X9 = X11|        &   |X12 = X11 -> X9|\\
|X5 = X4 -> X4|   &   |X5 = Int<t> -> Int<t+3>|\\
\end{tabular}
\end{expansionno}
\end{changemargin}

We can then use unification to generate the substitutions for time expressions.
As a result, the following substitutions are created:

\begin{changemargin}{1cm}{0cm}
\begin{expansionno}{text only}
\begin{tabular}{l l}
|X0 = <t+2>|      &   |X1 = <t+2> -> <t+2> -> <t+4>| \\
|X2 = <t+2>|      &   |X3 = <t+2> -> <t+4>| \\
|X4 = <t+2>|      &   |X5 = <t+2> -> <t+3>| \\ 
|X6 = <t+3>|      &   |X7 = <t+2>| \\
|X8 = <t+2> -> <t+2> |   &   |X9 = <t+2>|\\
$\quad \:$ |-> <t+3> -> <t+4>| \\
|X10 = <t+2> -> <t+3> -> <t+4>|        &   |X11 = <t+3>|\\
|X12 = <t+3> -> <t+4>|   &   |X13 = <t+2> -> <t+3> -> <t+4>|\\
|X14 = <t+3> -> <t+4>|   &   |X15 = <t+4>|\\
\end{tabular}
\end{expansionno}
\end{changemargin}

The type of the |comp| function, after we combine the above substitution with the base type substitutions, is defined to be |X1 = Bool<t+2> -> Int<t+2> -> Int<t+4>|, which reflects the time-dependent behaviour of |comp|.
As mentioned before, we use flexible composition, and as such the type of |comp| reflects the described circuit of figure \ref{fig:compositionsel} on page \pageref{fig:compositionsel}.

Since all substitutions are written in terms of a single time variable, all time-dependent behaviour from every expression is known.
Since all time-dependent behaviour from every expressions is known, it should \textit{in principle} be possible to derive a circuit description from the type information.

\section{Conclusion}
Even though the implementation is not complete, we have shown that verification and inference of time-dependent behaviour is feasible.
The implementation is not as elegant as it could be however.
Since the implementation was mainly used as a tool to figure out how to verify and infer time-dependent behaviour, it was created without a detailled plan.

If a real implementation were to be made, the usage of \gls{smt}-solvers may not be needed.
While \gls{smt}-solvers allow us to define statements of first order logic, solving these statements does come at a cost.
The computational complexity of \gls{smt}-solvers is known to be non-polynomical, which might make them less suited for larger projects.
Moreover, since the constraints on time expressions are fairly simple, other methods could be used to check the types of expressions and determine register placement. 

The implementation shown here differs from the type system of chapter \ref{ch:typesystem} in a few aspects.
First, the implementation does not use a $\delta$ function to only allow construction of functions which include monotonic increase of delays.
As such, the given implementation might not be as robust as the type system presented earlier.
Instead, ascription is used to bind a type to a term.

Furthermore, in the type system of chapter \ref{ch:typesystem}, we do not use type variables, nor unification.
These are artifacts from adopting Pierce's algorithm, and not strictly needed for an implementation.
In addition, time variables are introduced through a separate term.
In the type system introduced earlier, time variables are scoped using universal and existential quantification as part of either constraints or polytemporal types.


%\section{Introduction}
%For the actual implementation I use DeBruijn indices, primarily so I do not have to deal with scoping problems while developing the timing extensions.
%This will of course make the parsing more complex, but seeing as parsing haskell-esque source code has been done before I hope this will prove only a small burden.
%Internally I simply represent DeBruijn indices as:
%\begin{code}
%type DeBruijn = Int
%\end{code}
%I use DeBruijn indices for a number of things:
%\begin{itemize}
%\item Refering a variable to its binder.
%\item Refering a time variable to its time quantifier.
%\item Refering a variables in a let expression to its definition.
%\end{itemize}
%
%Before going into further details I will first show how I deal with typechecking and checking the timing information.
%To show how the type checker is implemented the following picture shows the different steps in the typechecking process.
%Note that I currently do not have implemented the parsing part.
%\begin{figure}[H]
%\begin{tikzpicture}[scale=0.85,transform shape]
%
%  \path \blocktitle{1}{Parser}{};
%  \path (p1.south)+(0.0,-1.5)   \blocktitle{2}{Constraint generation}{Given a certain term, generate a list of constraints which need to hold in order for the term to have a type};
%  \path (p2.south)+(0.0,-1.5)   \blocktitle{3}{Split}{Splitting base types from timing information};
%  \path (p3.south)+(-3.5,-1.8)  \blocktitle{4}{Unification}{Unifies the constraints of base types, resulting in a mapping of type variables to types.};
%  \path (p3.south)+(3.5,-1.8)   \blocktitle{5}{Unification}{Unifies the constraints of timing information, resulting in a mapping of type variables to concrete time information and time constraints};
%  \path (p5.south)+(0,-1.5)     \blocktitle{6}{Timechecking}{Verifies the timing constraints};
%  \path (p6.south)+(-3.5,-1.5)  \blocktitle{7}{Merge}{Merges timing information with base types, possibly indicating errors if there is a mismatch};
%  \path [line] (p1.south) -- node [above] {} (p2) ;
%  \path [line] (p2.south) -- node [above] {} (p3) ;
%  \path [line] (p3.south) -- +(0.0,-0.5) -- +(-3.5,-0.5)
%    -- node [above, midway] {} (p4);
%  \path [line] (p3.south) -- +(0.0,-0.5) -- +(3.5,-0.5)
%    -- node [above, midway] {} (p5);
%  \path [line] (p5.south) -- node [above] {} (p6) ;
%  \path [line] (p6.south) -- +(0.0,-0.5) -- +(-3.5,-0.5)
%    -- node [above, midway] {} (p7);
% \path [line] (p4.south) -- +(0.0,-2.75) -- +(+3.5,-2.75)
%    -- node [above, midway] {} (p7);
%\end{tikzpicture}
%\end{figure}
%As seen in the flowchart, the entire typechecking part is split in two parts.
%The checking of timing is independent from regular typechecking.
%This approach has some advantages:
%\begin{itemize}
%\item Regular typechecking can be used on the base types, something which is well understood already.
%\item When merging the results from type and timechecking we can verify that the results from timechecking have the same structure as the ones from typechecking.
%      This provides a simple error detection method, increasing the confidence in correctness.
%\item If the timechecking algorithm is independent of typechecking the same approach may be used to augment other typecheckers with time information.
%\item Extending the timechecking part is easier.
%\end{itemize}
%
%Before explaining the details, I will first explain some basic abstraction mechanism, as unification is used more than once.
%To allow this the general structure of types has to be shared between timing information and base types.
%This can be done using a parameterized data type:
%\begin{code}
%type VariableIndex = Int
%
%data MetaType a     =   Arrow (MetaType a) (MetaType a)
%                    |   Var VariableIndex
%                    |   Concrete a
%\end{code}
%, with |VariableIndex| being a unique identifier used for type inference.
%
%We can then then easily split and combine base type information with timing information through a datatype:
%\begin{code}
%data Type   = Type BaseType TimeType
%            deriving (Eq,Show)
%
%data BaseType  =   TyBool
%                    |   TyInt
%                    deriving (Eq,Show)
%
%data TimedType  =   TimeBound TimeVariableIndex Offset
%                |   TimeLiteral Offset
%                |   TimeVar DeBruijn Offset
%                deriving (Eq,Show)
%\end{code}
%The |TimeType| can take on three different forms.
%The |TimeVar| constructor is only used in ascriptions. 
%Using a DeBruijn index it refers to a certain time quantifier ($\psi$ in the grammar)
%
%When generating the constraints this is transformed to the |TimeBound| form, using a unique variable indentifier.
%The last form is a literal, allowing concrete timing information in types.
%
%Since we are now able to easily go from one representation to another (merging and splitting) we can almost define a general implementation for unification.
%However, unification applied to |TimeType| is slightly different than |BaseType|.
%With |BaseType| when a constraint |Concrete x = Concrete y|, with $y$ and $x$ being |BaseType|, is unified the constraint is either thrown away when they are equal, or a type error occurs when they are not the same.
%For |TimeType| this is different however, as we cannot determine from a single constraint if the constraint actually holds.
%For instance, if we have the constraint $N_1 = N_2 + 1$, with $N_x$ being time variables, then we cannot know, just from this information, if the timing is correct.
%
%Before diving into the modification of the unification algorithm I will first determine a method how we can in fact figure out if timing is correct.
%The naive implementation would simply replace timevariables with literals when it encounters them.
%The problem with this approach is that we cannot distinguish anymore between a valid delay (introduced through ascription and bound to a function) or incorrect timing behaviour.
%Say for instance we have a function 
%\begin{code}
%foo :: Bool<n> -> Bool<n+1> -> Bool<n+2>
%foo _ y = y
%\end{code}
%When applied to a value with type |Bool<0>|, we can determine $n = 0$ and subsequently replace $n$ with $0$ in the constraints.
%The problem is, the resulting type as introduced with ascription should be |Bool<2>|, which is not the same as |y :: Bool<1>|. 
%We will run into the comparison of |Bool<1> = Bool <2>| at one point, which in this case is a valid delay.
%However, since we removed all time quantifiers we do not know anymore whether this was a legitimate time delay introduced by ascription, or an error.
%
%Instead, to deal with this problem I first started simply noting constraints.
%When a certain time quantifier is bound to a literal, instead of replacing the time variable with the literal, I replace the literal with the time variable and note the constraint.
%That way the information we need is conserved, as we need to distinguish between legitimate time delays within a function definition and actual type errors.
%There are basically three scenarios we can encounter when comparing time variables:
%\begin{itemize}
%\item A literal is compared to another literal. We can simply compare and error when they are not equal.
%\item A literal compared to a time variable. We can record the constraint and replace all literals with that specific time variable.
%\item A time variable compared to another time variable. This has two distinct scenarios: either the variables are equal (but offsets are not), or they are not equal. 
%      The first situation we can simply ignore, since delays are allowed within a function.
%      The second however, we can't ignore since no delays are allowed when composing functions.
%\end{itemize}
%
%There is a unforseen \todo{Ik ben hier net gister achtergekomen} problem with this approach however.
%Consider the following function:
%
%\begin{code}
%f :: Bool<n> -> Bool<n+1> -> Bool<n+4>
%g :: Bool<m> -> Bool<m+2> -> Bool<m+3>
%
%h   =   let     b   = True :: Bool<0>
%                g'  = g b
%                f'  = f b
%        in      \x -> g' (f' x)
%\end{code}
%, which will typecheck and have type |Bool<1> -> Bool<3>|, which is obviously wrong.
%This happens since, whenever we encounter a literal, all literals are bound to the same time variable.
%The types of |f'| after the substitution |m = 0| is made makes clear what is going on:
%\begin{code}
%f' :: Bool<m+1> -> Bool<m+4>
%g' :: Bool<m+2> -> Bool<m+3>
%\end{code}
%
%From the code it is clear that |f'|s resulting type cannot be used for |g'|, yet since we allow comparisons between two time variables to have different offsets this gives a wrong result.
%It could probably be determined if it is a real delay or a bad type from the ordering in the constraint (e.g. m+4 = m+2 vs m+2 = m+4).
%But since it is pretty clearly meant as an equivalence relation I do not want to depend on the order of constraints. 
%It would probably introduce bugs as well since it is hard to guarantee a certain order without letting go of the simple one to one relation used in constraints.
%
%Instead of rewriting substitutions and constraints to allow for introducing delays at the typelevel I chose to use a different approach.
%The principle is the same as before, however, when comparing time variables with literals and other time variables I chose to simply note the constraint and not do any rewriting.
%This results in both a set of substitutions, and a set of timing constraints. 
%The timing constraints can be checked independently, resulting in a mapping between time variables and actual time moments.\footnote{Het probleem van het detecteren van een delay is nog niet weg, echter omdat we nu wel exact onderscheid kunnen maken tussen verschillende tijdsvariabelen is het mogelijk om het wel te detecteren}
%These can then be substituted in the set of substitutions, resulting in a complete type. 
%
%\subsection{Unification}
%As mentioned by above, the actual unification algorithm is the same, except when |Concrete| types are compared.
%To facilitate this I have defined a typeclass which allows this comparison to be different, together with an abstract mechanism to store possible results from this comparison:
%\begin{code}
%type Substitution a = (MetaType a, MetaType a)
%
%data BaseRecord = BaseRecord [Substitution BaseType]
%
%data TimeRecord         =       TimeRecord 
%                        { timeSubs :: [Substitution TimeType]
%                        , timeVars :: [(TimeType,TimeType)] 
%                        }
%
%class Eq a => Substitutable z a where
%    add :: Substitution a -> z -> z
%    apply :: ([Substitution a] -> [Substitution a]) -> z -> z 
%    match :: MetaType a -> MetaType a -> z -> z 
%
%instance Substitutable TimeRecord TimeType where
%    add x tr = tr { timeSubs = x : (timeSubs tr) }
%    apply f tr = tr { timeSubs = f $ timeSubs tr }
%    match = ... -- left out on purpose
%
%instance Substitutable BaseRecord BaseType where
%    add x (BaseRecord xs) = BaseRecord (x:xs)
%    apply f (BaseRecord xs) = BaseRecord $ f xs
%    match (Concrete x) (Concrete y) tr
%        | x == y = tr
%        | otherwise = error "x /= y"
%\end{code}
%
%These functions are fairly straightforward.
%|add| adds a substitution to a data structure.
%|apply| applies a certain transformation of substitutions to the data structure
%|match| matches two Concrete types and possibly updates a data structure which holds relevant data.
%
%The unification algorithm can then be used for both base types and timing information:
%\begin{code}
%unify :: (Substitutable z a) => [Constraint a] -> z -> z
%unify [] r = id r
%unify (c:cs) r = case c of
%    (Concrete t1, Concrete t2)      -> unify cs $ match (Concrete t1) (Concrete t2) r
%    (Arrow s1 s2, Arrow t1 t2)      -> unify ((s1,t1) : (s2,t2) : cs) r
%    (tyS@(Var idS), tyT      )
%        | tyS == tyT                ->  unify cs r
%        | not $ idS `isFVIn` tyT    ->  let     cs' = (tyS |-> tyT) cs
%                                                r'  = add (tyS,tyT) $ apply (tyS |-> tyT) r
%                                        in      unify cs' r'
%
%    (tyS, tyT@(Var idT)      )      -> unify ((tyT,tyS) : cs) r
%    (t1,t2                   )      -> error "not unifiable "
%\end{code}
