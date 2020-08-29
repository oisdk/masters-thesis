\begin{code}
{-# OPTIONS --cubical --safe --postfix-projections #-}

module Cardinality.Finite.ManifestEnumerable where

open import Prelude

import Cardinality.Finite.ManifestEnumerable.Inductive as 𝕃
import Cardinality.Finite.ManifestEnumerable.Container as ℒ

open import Cardinality.Finite.ManifestEnumerable.Isomorphism

open import Data.Fin
open import Data.Sigma.Properties
open import HITs.PropositionalTruncation
open import HITs.PropositionalTruncation.Sugar

module _ where
  open ℒ
  ℰ⇔Fin↠ :
\end{code}
%<*manifest-enum-surj>
\begin{code}
    ℰ A ⇔ Σ[ n ⦂ ℕ ] (Fin n ↠ A)
\end{code}
%</manifest-enum-surj>
\begin{code}
  ℰ⇔Fin↠ = reassoc

module _ where
  open 𝕃
  open import Literals.Number
  open import Data.Nat.Literals
  open import Data.Fin.Literals
  open import Data.List.Syntax

  open import Cubical.HITs.S1 hiding (inv; isConnectedS¹)

  private
    module S1ConnectedDisplay where
      import Cubical.HITs.S1.Properties as S1Properties
\end{code}
%<*s1-connected>
\begin{code}
      isConnectedS¹ : (s : S¹) → ∥ base ≡ s ∥
\end{code}
%</s1-connected>
\begin{code}
      isConnectedS¹ = S1Properties.isConnectedS¹

  open import Cubical.HITs.S1.Properties
  ∥map∥ = _∥$∥_
\end{code}
%<*circle-is-manifest-enum>
\begin{code}
  ℰ⟨S¹⟩ : ℰ S¹
  ℰ⟨S¹⟩ .fst  = [ base ]
  ℰ⟨S¹⟩ .snd  = ∥map∥ (0 ,_) ∘ isConnectedS¹
\end{code}
%</circle-is-manifest-enum>
\begin{code}

  open import HITs.PropositionalTruncation.Properties
  open import Cardinality.Finite.SplitEnumerable.Inductive
  open import Cardinality.Finite.SplitEnumerable
  open import Cardinality.Finite.SplitEnumerable.Isomorphism

  ℰ⇒ℰ! : Discrete A → ℰ A → ℰ! A
  ℰ⇒ℰ! _≟_ E .fst = E .fst
  ℰ⇒ℰ! _≟_ E .snd x = recompute ((_≟ x) ∈? E .fst) (E .snd x)

  ℰ!⇒ℰ : ℰ! A → ℰ A
  ℰ!⇒ℰ E .fst = E .fst
  ℰ!⇒ℰ E .snd x = ∣ E .snd x ∣

  _∥Σ∥_ : {B : A → Type b} → ℰ A → ((x : A) → ℰ (B x)) → ℰ (Σ A B)
  (xs ∥Σ∥ ys) .fst = sup-Σ (xs .fst) (fst ∘ ys)
  (xs ∥Σ∥ ys) .snd (x , y) = ⦇ (cov-Σ x y (xs .fst) (fst ∘ ys)) (xs .snd x) (ys x .snd y) ⦈

  open import Cubical.Foundations.HLevels using (isOfHLevelΣ; hLevelPi)
  open import Cubical.Data.List.Properties using (isOfHLevelList)

  isSet⟨ℰ⟩ : isSet A → isSet (ℰ A)
  isSet⟨ℰ⟩ isSetA =
    isOfHLevelΣ 2
      (isOfHLevelList 0 isSetA)
      λ _ → isProp→isSet (hLevelPi 1 λ _ → squash)

  open import Relation.Nullary.Omniscience
  open import Data.List.Relation.Unary

  private variable p : Level

  ℰ⇒Omniscient : ℰ A → Omniscient p A
  ℰ⇒Omniscient xs P? =
    ∣ Exists.◇? _ P? (xs .fst)
      ∣yes⇒ (λ { (n , p) → (xs .fst ! n , p)})
      ∣no⇒ (λ { ¬P∈xs (x , p) → refute-trunc ¬P∈xs (map₂ (flip (subst _) p ∘ sym) ∥$∥ xs .snd x)  })
\end{code}
