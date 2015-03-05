%include polycode.fmt
%format s = "\sigma"
%format s_1 = "\sigma_1"
%format s_2 = "\sigma_2"
%format t = "\tau"
%format t1 = "\tau_1"
%format t2 = "\tau_2"
%format C = "\mathcal{C}"
%format <</- = "\notin"
%format |-> = "\mapsto"
%format X   = "\psi"

\begin{changemargin}{1cm}{0cm}
\begin{expansionno}{text only}
\begin{code}
unify []      = []
unify (t <= s : C) 
  | t == s    =   unify C 
  | t == X and X <</- FV(s)  
              =   let C' = [t |-> s] C
                  in  [t |-> s] : (unify C')
  | s == X and X <</- FV(s)  
              =   let C' = [s |-> t] C
                  in  [s |-> t] : (unify C')
  | otherwise =   error "Not well-typed"
\end{code}
\end{expansionno}
\end{changemargin}


