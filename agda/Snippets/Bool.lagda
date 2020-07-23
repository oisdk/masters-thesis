\begin{code}
{-# OPTIONS --cubical --safe #-}

module Snippets.Bool where

open import Level

private
  module BoolDefn where
\end{code}
%<*bool-def>
\begin{code}
    data Bool : Type₀ where
      false  : Bool
      true   : Bool
\end{code}
%</bool-def>
\begin{code}

open import Data.Bool
open import Prelude hiding (_∧_)

infixl 6 _∧_
\end{code}
%<*and-def>
\begin{code}
_∧_ : Bool → Bool → Bool
false  ∧ false  = false
false  ∧ true   = false
true   ∧ false  = false
true   ∧ true   = true
\end{code}
%</and-def>
\begin{code}
open import Cardinality.Finite.SplitEnumerable
open import Cardinality.Finite.SplitEnumerable.Search
open import Cardinality.Finite.SplitEnumerable.Instances
open import Cardinality.Finite.SplitEnumerable.Inductive
open import Cardinality.Finite.SplitEnumerable.Isomorphism
open import Cardinality.Finite.ManifestBishop
open import Data.Bool.Properties using (discreteBool)

infixl 4 _≟_
_≟_ = discreteBool
\end{code}
%<*bool-assoc-auto-proof>
\begin{code}
∧-assoc : ∀ x y z → (x ∧ y) ∧ z ≡ x ∧ (y ∧ z)
∧-assoc = ∀↯ⁿ 3 λ x y z → (x ∧ y) ∧ z ≟ x ∧ (y ∧ z)
\end{code}
%</bool-assoc-auto-proof>
%<*some-assoc>
\begin{code}
some-assoc : Σ[ f ⦂ (Bool → Bool → Bool) ] ∀ x y z → f (f x y) z ≡ f x (f y z)
some-assoc = ∃↯ⁿ 1 λ f → ∀?ⁿ 3 λ x y z → f (f x y) z ≟ f x (f y z)
\end{code}
%</some-assoc>
%<*obvious>
\begin{code}
obvious : true ∧ false ≡ false
obvious = refl
\end{code}
%</obvious>
\begin{code}
private
 module SumDec where
\end{code}
%<*is-true>
\begin{code}
  True : Dec A → Type₀
  True (yes  _) = ⊤
  True (no   _) = ⊥
\end{code}
%</is-true>
%<*from-true>
\begin{code}
  toWitness :  (decision : Dec A) →
               { _ : True decision } → A
  toWitness (yes x) = x
\end{code}
%</from-true>
\begin{code}
open import Relation.Nullary.Decidable.Logic
open import Relation.Nullary.Decidable

from-true : (dec : Dec A) → { _ : T (does dec) } → A
from-true (yes p) = p
\end{code}
%<*extremely-obvious>
\begin{code}
extremely-obvious : true ≢ false
extremely-obvious = from-true (! (true ≟ false))
\end{code}
%</extremely-obvious>
\begin{code}
module PreInst′ where
  open PreInst
\end{code}
%<*pre-inst-proof>
\begin{code}
  ∧-idem : ∀ x → x ∧ x ≡ x
  ∧-idem = ∀↯ ℰ!⟨2⟩ λ x → x ∧ x ≟ x
\end{code}
%</pre-inst-proof>
\begin{code}
open WithInst
\end{code}
%<*with-inst-proof>
\begin{code}
∧-idem : ∀ x → x ∧ x ≡ x
∧-idem = ∀↯ λ x → x ∧ x ≟ x
\end{code}
%</with-inst-proof>
\begin{code}
module BadCurrying where
\end{code}
%<*and-comm>
\begin{code}
  ∧-comm : ∀ x y → x ∧ y ≡ y ∧ x
  ∧-comm = curry (∀↯ (uncurry (λ x y → x ∧ y ≟ y ∧ x )))
\end{code}
%</and-comm>
\begin{code}
open import Data.Fin
\end{code}
%<*finite-sigma-inst>
\begin{code}
_ : ℰ! (Σ[ s ⦂ Bool ] (if s then Fin 3 else Fin 4))
_ = it
\end{code}
%</finite-sigma-inst>
%<*and-comm-auto>
\begin{code}
∧-comm : ∀ x y → x ∧ y ≡ y ∧ x
∧-comm = ∀↯ⁿ 2 λ x y → x ∧ y ≟ y ∧ x
\end{code}
%</and-comm-auto>
