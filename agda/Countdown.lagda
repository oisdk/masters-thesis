\begin{code}
{-# OPTIONS --cubical --postfix-projections --safe #-}

module Countdown where

open import Prelude
open import Data.List
open import Data.Fin

open import Data.Nat using (_+_; _*_; _∸_; _÷_; rem)
open import Data.Nat.Properties using (pred; _≡ᴮ_; _<ᴮ_; discreteℕ)
open import Data.Fin.Properties using (FinToℕ)
open import Dyck
open import Data.Vec.Iterated

\end{code}
%<*ops-def>
\begin{code}
data Op : Type₀ where
  +′ ×′ -′ ÷′ : Op
\end{code}
%</ops-def>
\begin{code}
private
  variable
    n m k : ℕ

Subseq : ℕ → Type₀
Subseq = Vec Bool

private
  module WrongPerm where
\end{code}
%<*wrong-perm>
\begin{code}
    Perm : ℕ → Type₀
    Perm n = Fin n → Fin n
\end{code}
%</wrong-perm>
\begin{code}
private
  module IsoPerm where
\end{code}
%<*isomorphism>
\begin{code}
    Isomorphism : Type a → Type b → Type (a ℓ⊔ b)
    Isomorphism A B = Σ[ f ⦂ (A → B) ] Σ[ g ⦂ (B → A) ] (f ∘ g ≡ id) × (g ∘ f ≡ id)
\end{code}
%</isomorphism>
%<*iso-perm>
\begin{code}
    Perm : ℕ → Type₀
    Perm n = Isomorphism (Fin n) (Fin n)
\end{code}
%</iso-perm>
%<*perm-def>
\begin{code}
Perm : ℕ → Type₀
Perm zero     = ⊤
Perm (suc n)  = Fin (suc n) × Perm n
\end{code}
%</perm-def>
\begin{code}
private
  variable ns : List ℕ

count : Subseq n → ℕ
count = foldr′ (λ x xs → bool 0 1 x + xs) 0
\end{code}
%<*expr-def>
\begin{code}
ExprTree : ℕ → Type₀
ExprTree zero     = ⊥
ExprTree (suc n)  = Dyck 0 n × Vec Op n

Transformation : List ℕ → Type₀
Transformation ns =
  Σ[ s ⦂ Subseq (length ns) ]
    let n = count s
    in Perm n × ExprTree n
\end{code}
%</expr-def>
\begin{code}
open import Cardinality.Finite.SplitEnumerable
open import Cardinality.Finite.SplitEnumerable.Inductive
open import Cardinality.Finite.SplitEnumerable.Isomorphism
open import Function.Surjective.Properties

private
  module OpSlop where
    open import Literals.Number
    open import Data.Nat.Literals
    open import Data.Fin.Literals
\end{code}
%<*op-slop>
\begin{code}
    ℰ!⟨Op⟩ : ℰ! Op
    ℰ!⟨Op⟩ .fst = +′ ∷ +′ ∷ ×′ ∷ -′ ∷ ÷′ ∷ []
    ℰ!⟨Op⟩ .snd +′  = 0 , refl
    ℰ!⟨Op⟩ .snd ×′  = 2 , refl
    ℰ!⟨Op⟩ .snd -′  = 3 , refl
    ℰ!⟨Op⟩ .snd ÷′  = 4 , refl
\end{code}
%</op-slop>
\begin{code}
open import Data.List using (tabulate)
open import Data.List.Membership using (fin∈tabulate)

import Data.Unit.UniversePolymorphic as Poly

ℰ!⟨Poly⊤⟩ : ∀ {ℓ} → ℰ! (Poly.⊤ {ℓ})
ℰ!⟨Poly⊤⟩ .fst = _ ∷ []
ℰ!⟨Poly⊤⟩ .snd _ = f0 , refl
\end{code}
%<*vec-fin>
\begin{code}
ℰ!⟨Vec⟩ : ℰ! A → ℰ! (Vec A n)
ℰ!⟨Vec⟩ {n = zero   } ℰ!⟨A⟩ = ℰ!⟨Poly⊤⟩
ℰ!⟨Vec⟩ {n = suc n  } ℰ!⟨A⟩ = ℰ!⟨A⟩ |×| ℰ!⟨Vec⟩ ℰ!⟨A⟩
\end{code}
%</vec-fin>
\begin{code}
ℰ!⟨Subseq⟩ : ℰ! (Subseq n)
ℰ!⟨Subseq⟩ = ℰ!⟨Vec⟩ ℰ!⟨2⟩
\end{code}
%<*perm-fin>
\begin{code}
ℰ!⟨Perm⟩ : ℰ! (Perm n)
ℰ!⟨Perm⟩ {n = zero   } = ℰ!⟨⊤⟩
ℰ!⟨Perm⟩ {n = suc n  } = ℰ!⟨Fin⟩ |×| ℰ!⟨Perm⟩
\end{code}
%</perm-fin>
\begin{code}
module _ where
  open import Literals.Number
  open import Data.Fin.Literals
\end{code}
%<*op-fin>
\begin{code}
  ℰ!⟨Op⟩ : ℰ! Op
  ℰ!⟨Op⟩ .fst = +′ ∷ ×′ ∷ -′ ∷ ÷′ ∷ []
  ℰ!⟨Op⟩ .snd +′  = 0 , refl
  ℰ!⟨Op⟩ .snd ×′  = 1 , refl
  ℰ!⟨Op⟩ .snd -′  = 2 , refl
  ℰ!⟨Op⟩ .snd ÷′  = 3 , refl
\end{code}
%</op-fin>
\begin{code}
\end{code}
%<*expr-finite>
\begin{code}
ℰ!⟨ExprTree⟩ : ℰ! (ExprTree n)
ℰ!⟨ExprTree⟩ {n = zero } = ℰ!⟨⊥⟩
ℰ!⟨ExprTree⟩ {n = suc n} = ℰ!⟨Dyck⟩ |×| ℰ!⟨Vec⟩ ℰ!⟨Op⟩

ℰ!⟨Transformation⟩ : ℰ! (Transformation ns)
ℰ!⟨Transformation⟩ = ℰ!⟨Subseq⟩ |Σ| λ _ → ℰ!⟨Perm⟩ |×| ℰ!⟨ExprTree⟩
\end{code}
%</expr-finite>
\begin{code}
runSubseq : (xs : List A) → (ys : Subseq (length xs)) → Vec A (count ys)
runSubseq []       ys = _
runSubseq (x ∷ xs) (false , snd₁) = runSubseq xs snd₁
runSubseq (x ∷ xs) (true , snd₁) = x , runSubseq xs snd₁

insert : A → Fin (suc n) → Vec A n → Vec A (suc n)
insert x f0 xs = x , xs
insert {n = suc _} x (fs i) (x₂ , xs) = x₂ , insert x i xs

runPerm : Perm n → Vec A n → Vec A n
runPerm {n = zero} ps _ = _
runPerm {n = suc n} (fst₁ , snd₁) (x , xs) = insert x fst₁ (runPerm snd₁ xs)

transform : (xs : List ℕ) → Transformation xs → Tree Op ℕ
transform xs (subseq , rest) with count subseq | runSubseq xs subseq
transform xs (subseq , (perm , tree , ops)) | suc n | ys = fromDyck tree ops (runPerm perm ys)
\end{code}
%<*app-op>
\begin{code}
_!⟨_⟩!_ : ℕ → Op → ℕ → Maybe ℕ
x !⟨ +′ ⟩! y = just $! (x + y)
x !⟨ ×′ ⟩! y = just $! (x * y)
x !⟨ -′ ⟩! y =
  if x <ᴮ y
    then nothing
    else just $! (x ∸ y)
x !⟨ ÷′ ⟩! zero = nothing
x !⟨ ÷′ ⟩! suc y =
  if rem x (suc y) ≡ᴮ 0
    then just $! (x ÷ suc y)
    else nothing
\end{code}
%</app-op>
%<*eval>
\begin{code}

eval : Tree Op ℕ → Maybe ℕ
eval (leaf x) = just x
eval (xs ⟨ op ⟩ ys) = do
    x ← eval xs
    y ← eval ys
    x !⟨ op ⟩! y
\end{code}
%</eval>
\begin{code}
  where
  open import Data.Maybe.Sugar

open import Data.Maybe.Properties using (discreteMaybe)

Solution : List ℕ → ℕ → Type₀
\end{code}
%<*solution-type>
\begin{code}
Solution ns n = Σ[ e ⦂ Transformation ns ] (eval (transform ns e) ≡ just n)
\end{code}
%</solution-type>
\begin{code}

solution? : ∀ n → (e : Transformation ns) → Dec (eval (transform ns e) ≡ just n)
solution? {ns} n e = discreteMaybe discreteℕ (eval (transform ns e)) (just n)

ℰ!⟨Solutions⟩ :
\end{code}
%<*finite-solution>
\begin{code}
  ℰ! (Solution ns n)
\end{code}
%</finite-solution>
\begin{code}
ℰ!⟨Solutions⟩ {ns = ns} = filter-subobject (λ _ → isSetMaybe _ _) (solution? {ns = ns} _) (ℰ!⟨Transformation⟩ {ns = ns})
  where
  isSetMaybe : isSet (Maybe ℕ)
  isSetMaybe = Discrete→isSet (discreteMaybe discreteℕ)

data Disp : Type₀ where
  lit : ℕ → Disp
  _⟨+⟩_ : Disp → Disp → Disp
  _⟨*⟩_ : Disp → Disp → Disp
  _⟨-⟩_ : Disp → Disp → Disp
  _⟨÷⟩_ : Disp → Disp → Disp

appDispOp : Op → Disp → Disp → Disp
appDispOp +′ = _⟨+⟩_
appDispOp ×′ = _⟨*⟩_
appDispOp -′ = _⟨-⟩_
appDispOp ÷′ = _⟨÷⟩_

dispTree : Tree Op ℕ → Disp
dispTree (leaf x) = lit $! x
dispTree (xs ⟨ o ⟩ ys) = (appDispOp o $! dispTree xs) $! dispTree ys

open import Data.List.Syntax
\end{code}
%<*example-solution>
\begin{code}
exampleSolutions : ℰ! (Solution [ 1 , 3 , 7 , 10 , 25 , 50 ] 765)
exampleSolutions = ℰ!⟨Solutions⟩
\end{code}
%</example-solution>
\begin{code}

example : List Disp
example = map (dispTree ∘ transform [ 1 , 3 , 7 , 10 , 25 , 50 ] ∘ fst) (take 1 (fst exampleSolutions))

-- Uncomment for an error which contains the solution
-- _ : example ≡ lit 0 ∷ []
-- _ = refl
\end{code}
