\begin{code}
{-# OPTIONS --cubical --safe --postfix-projections #-}

module Cardinality.Finite.Kuratowski where

open import Prelude
open import Algebra.Construct.Free.Semilattice
open import Algebra.Construct.Free.Semilattice.Relation.Unary

open import Cardinality.Finite.ManifestEnumerable
open import Cardinality.Finite.ManifestEnumerable.Inductive renaming (_∈_ to _L∈_)

open import HITs.PropositionalTruncation
import HITs.PropositionalTruncation as PropTrunc
open import HITs.PropositionalTruncation.Sugar
open import Data.Fin

𝒦ᶠ : Type a → Type a
\end{code}
%<*kuratowski-finite-def>
\begin{code}
𝒦ᶠ A = Σ[ xs ⦂ 𝒦 A ] ((x : A) → x ∈ xs)
\end{code}
%</kuratowski-finite-def>
\begin{code}

𝒦ᶠ⇒∥ℰ∥ : 𝒦ᶠ A → ∥ ℰ A ∥
𝒦ᶠ⇒∥ℰ∥ K = map₂ (λ p x → p x (K .snd x)) ∥$∥ ∥ enum ∥⇓ (K .fst)
  where
  enum : xs ∈𝒦 A ⇒∥ ∥ Σ[ ys ⦂ List A ] (∀ x → x ∈ xs → ∥ x L∈ ys ∥) ∥ ∥
  ∥ enum ∥-prop = squash
  ∥ enum ∥[] = ∣ [] , (λ _ ()) ∣
  ∥ enum ∥ x ∷ xs ⟨ Pxs ⟩ = cons ∥$∥ Pxs
    where
    cons : _
    cons (ys , p) .fst = x ∷ ys
    cons (ys , p) .snd z zs = zs >>= either′ (∣_∣ ∘ (f0 ,_)) ((push ∥$∥_) ∘ p z)

open import Algebra.Construct.Free.Semilattice.Extensionality
open import Algebra.Construct.Free.Semilattice.FromList
open import Data.Sigma.Properties

isProp𝒦ᶠ : isProp (𝒦ᶠ A)
isProp𝒦ᶠ Kˣ Kʸ =
  Σ≡Prop
    (λ K p q i x → isProp-◇ {xs = K} (p x) (q x) i)
    {Kˣ} {Kʸ}
    (extensional (fst Kˣ) (fst Kʸ) λ x → const (Kʸ .snd x) iff const (Kˣ .snd x))

ℰ⇒𝒦 : ℰ A → 𝒦ᶠ A
ℰ⇒𝒦 E .fst = fromList (E .fst)
ℰ⇒𝒦 E .snd x = ∈List⇒∈𝒦 (E .fst) (E .snd x)

open import Cubical.HITs.S1 using (S¹)

𝒦ᶠ⟨S¹⟩ : 𝒦ᶠ S¹
𝒦ᶠ⟨S¹⟩ = ℰ⇒𝒦 ℰ⟨S¹⟩
∥ℰ∥⇔𝒦 :
\end{code}
%<*manifest-enum-kuratowski>
\begin{code}
 ∥ ℰ A ∥ ⇔ 𝒦ᶠ A
\end{code}
%</manifest-enum-kuratowski>
\begin{code}
∥ℰ∥⇔𝒦 .fun = PropTrunc.rec isProp𝒦ᶠ ℰ⇒𝒦
∥ℰ∥⇔𝒦 .inv = 𝒦ᶠ⇒∥ℰ∥
∥ℰ∥⇔𝒦 .leftInv x = squash _ x
∥ℰ∥⇔𝒦 .rightInv x = isProp𝒦ᶠ _ x

open import Cardinality.Finite.Cardinal using (𝒞; 𝒞⇒Discrete)
open import Cardinality.Finite.ManifestBishop using (ℬ⇒ℰ!; ℰ!⇒ℬ)
open import Cardinality.Finite.ManifestEnumerable using (ℰ!⇒ℰ; ℰ⇒ℰ!)
open import Relation.Nullary.Discrete.Properties

𝒞⇔𝒦×Discrete :
\end{code}
%<*card-iso-kuratowski>
\begin{code}
  𝒞 A ⇔ 𝒦ᶠ A × Discrete A
\end{code}
%</card-iso-kuratowski>
\begin{code}
𝒞⇔𝒦×Discrete .fun ca .fst = ∥ℰ∥⇔𝒦 .fun (ℰ!⇒ℰ ∘ ℬ⇒ℰ! ∥$∥ ca)
𝒞⇔𝒦×Discrete .fun ca .snd = 𝒞⇒Discrete ca
𝒞⇔𝒦×Discrete .inv (ka , d) = ℰ!⇒ℬ ∘ ℰ⇒ℰ! d ∥$∥ ∥ℰ∥⇔𝒦 .inv ka
𝒞⇔𝒦×Discrete .rightInv _ = isOfHLevelΣ 1 isProp𝒦ᶠ (λ _ → isPropDiscrete) _ _
𝒞⇔𝒦×Discrete .leftInv  _ = squash _ _

open import Relation.Nullary.Decidable.Properties
open import Relation.Nullary.Omniscience
open import HITs.PropositionalTruncation.Properties

private variable p : Level

𝒦ᶠ⇒Exhaustible : 𝒦ᶠ A → Exhaustible p A
𝒦ᶠ⇒Exhaustible K P? =
  ∣ ◻? P? (K .fst)
    ∣yes⇒ (λ ◻Pxs x → recompute (P? x) (P∈◇ x (K .fst) (K .snd x) ◻Pxs))
    ∣no⇒ λ ¬◻Pxs ∀P → ¬◻Pxs (map-◻ ∀P (K .fst))

\end{code}
%<*kuratowski-prop-omniscient>
\begin{code}
𝒦ᶠ⇒Prop-Omniscient : 𝒦ᶠ A → Prop-Omniscient p A
𝒦ᶠ⇒Prop-Omniscient K P? =
  PropTrunc.rec
    (isPropDec squash)
    (map-dec ∣_∣ refute-trunc ∘ λ xs → ℰ⇒Omniscient xs P?)
    (𝒦ᶠ⇒∥ℰ∥ K)
\end{code}
%</kuratowski-prop-omniscient>
