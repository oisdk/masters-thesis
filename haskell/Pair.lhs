%include polycode.fmt
%subst keyword a = "\AgdaKeyword{" a "}"
\begin{code}
module Pair where
\end{code}
%<*fst>
\begin{code}
fst :: (a, b) -> a
fst (x, y) = x
\end{code}
%</fst>
\begin{code}
fst' ::
\end{code}
%<*fst-ty>
\begin{code}
  (a, b) -> a
\end{code}
%</fst-ty>
\begin{code}
fst' = fst
\end{code}