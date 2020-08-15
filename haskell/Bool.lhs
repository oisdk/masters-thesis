%include polycode.fmt
%subst keyword a = "\AgdaKeyword{" a "}"
%format not = "\Varid{not} "

\begin{code}
module Bool where
\end{code}
%<*bool-def>
\begin{code}
data Bool :: Type where
  False  :: Bool
  True   :: Bool
\end{code}
%</bool-def>
%<*bool-val>
\begin{code}
aBoolean :: Bool
aBoolean = True
\end{code}
%</bool-val>
%<*not-func>
\begin{code}
not :: Bool -> Bool
not True   = False
not False  = True
\end{code}
%</not-func>
