%include polycode.fmt
%subst keyword a = "\AgdaKeyword{" a "}"

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