\begin{code}
{-# OPTIONS --cubical --safe #-}

module Cardinality.Finite.SplitEnumerable.Search where

open import Prelude
open import Cardinality.Finite.SplitEnumerable
open import Cardinality.Finite.SplitEnumerable.Inductive
open import Cardinality.Finite.ManifestEnumerable using (ℰ⇒Omniscient; ℰ!⇒ℰ)
open import Data.Product.NAry
open import Relation.Nullary.Decidable.Properties
open import Data.Fin
open import Relation.Nullary.Omniscience
open import Cardinality.Finite.SplitEnumerable.Isomorphism
open import HITs.PropositionalTruncation
open import HITs.PropositionalTruncation.Properties

private variable p : Level

ℰ!⇒Omniscient : ℰ! A → Omniscient p A
ℰ!⇒Omniscient = ℰ⇒Omniscient ∘ ℰ!⇒ℰ

ℰ!⇒Exhaustible : ℰ! A → Exhaustible p A
ℰ!⇒Exhaustible = Omniscient→Exhaustible ∘ ℰ!⇒Omniscient

ℰ!⟨fib⟩ : (f : A → B) → (y : B) → ℰ! A → ℰ! B → ℰ! ∥ fiber f y ∥
ℰ!⟨fib⟩ f y xs ys with ℰ!⇒Omniscient xs λ x → ℰ!⇒Discrete (𝕃⇔ℒ⟨ℰ!⟩ .fun ys) (f x) y
ℰ!⟨fib⟩ f y xs ys | yes p = ∣ p ∣ ∷ [] , λ _ → f0 , squash _ _
ℰ!⟨fib⟩ f y xs ys | no ¬p = [] , ⊥-elim ∘ refute-trunc ¬p

tup-inst′ : ∀ n {ls} {Xs : Types (suc n) ls} → ⦅ map-types ℰ! Xs ⦆⁺ → ℰ! ⦅ Xs ⦆⁺
tup-inst′ zero x = x
tup-inst′ (suc n) (x , xs) = x |×| tup-inst′ n xs

tup-inst : ∀ n {ls} {Xs : Types n ls} → ⦅ map-types ℰ! Xs ⦆ → ℰ! ⦅ Xs ⦆
tup-inst zero xs = _ ∷ [] , λ _ → f0 , refl
tup-inst (suc n) xs = tup-inst′ n xs

Dec⇔ : (B ⇔ A) → Dec A → Dec B
Dec⇔ A⇔B = ⟦yes A⇔B .inv ,no A⇔B .fun ⟧

module _ {a p} {A : Type a} {P : A → Type p} where
\end{code}
%<*forall-ask>
\begin{code}
  ∀? :  ℰ! A →
        (∀ x → Dec (P x)) →
        Dec (∀ x → P x)
  ∀? ℰ!⟨A⟩ = ℰ!⇒Exhaustible ℰ!⟨A⟩
\end{code}
%</forall-ask>
%<*exists-ask>
\begin{code}
  ∃? :  ℰ! A →
        (∀ x → Dec (P x)) →
        Dec (∃[ x ] P x)
  ∃? ℰ!⟨A⟩ = ℰ!⇒Omniscient ℰ!⟨A⟩
\end{code}
%</exists-ask>
\begin{code}
module PreInst {a p} {A : Type a} {P : A → Type p} where
\end{code}
%<*forall-zap>
\begin{code}
  ∀↯ :  (ℰ!⟨A⟩ : ℰ! A) →
        (P? : ∀ x → Dec (P x)) →
        ⦃ _ : True (∀? ℰ!⟨A⟩ P?) ⦄ →
        ∀ x → P x
  ∀↯ _ _ ⦃ t ⦄ = toWitness t
\end{code}
%</forall-zap>
%<*exists-zap>
\begin{code}
  ∃↯ :  (ℰ!⟨A⟩ : ℰ! A) →
        (P? : ∀ x → Dec (P x)) →
        ⦃ _ : True (∃? ℰ!⟨A⟩ P?) ⦄ →
        ∃[ x ] P x
  ∃↯ _ _ ⦃ t ⦄ = toWitness t
\end{code}
%</exists-zap>
\begin{code}
module WithInst {a p} {A : Type a} {P : A → Type p} where
\end{code}
%<*forall-zap-inst>
\begin{code}
  ∀↯ :  ⦃ ℰ!⟨A⟩ : ℰ! A ⦄ →
        (P? : ∀ x → Dec (P x)) →
        ⦃ _ : True (∀? ℰ!⟨A⟩ P?) ⦄ →
        ∀ x → P x
  ∀↯ _ ⦃ t ⦄ = toWitness t
\end{code}
%</forall-zap-inst>
%<*exists-zap-inst>
\begin{code}
  ∃↯ :  ⦃ ℰ!⟨A⟩ : ℰ! A ⦄ →
        (P? : ∀ x → Dec (P x)) →
        ⦃ _ : True (∃? ℰ!⟨A⟩ P?) ⦄ →
        ∃[ x ] P x
  ∃↯ _ ⦃ t ⦄ = toWitness t
\end{code}
%</exists-zap-inst>
\begin{code}
module _ (n : ℕ)
         {ls ℓ}
         {Xs : Types n ls}
         {P : ⦅ Xs ⦆ → Type ℓ}
         where
  ∀?ⁿ  :   ⦅ map-types ℰ! Xs ⦆[ inst ]→
           xs ⦂⦅ Xs ⦆Π[ expl ]→
           Dec (P xs) [ expl ]→
           Dec (xs ⦂⦅ Xs ⦆Π[ expl ]→ P xs)
  ∀?ⁿ  =  [ n ^ inst $] .inv λ fs
       →  Dec⇔ Π[ n ^ expl $]
       ∘  Omniscient→Exhaustible (ℰ!⇒Omniscient (tup-inst n fs))
       ∘  Π[ n ^ expl $] .fun
\end{code}
%<*exists-q-n>
\begin{code}
  ∃?ⁿ  :   ⦅ map-types ℰ! Xs ⦆[ inst ]→
           xs ⦂⦅ Xs ⦆Π[ expl ]→
           Dec (P xs) [ expl ]→
           Dec (Σ ⦅ Xs ⦆ P)
  ∃?ⁿ  =  [ n ^ inst $] .inv λ fs
       →  ℰ!⇒Omniscient (tup-inst n fs)
       ∘  Π[ n ^ expl $] .fun
\end{code}
%</exists-q-n>
\begin{code}
  ∀↯ⁿ : insts ⦂⦅ map-types ℰ! Xs ⦆Π[ inst ]→
      ( (P? : xs ⦂⦅ Xs ⦆Π[ expl ]→ Dec (P xs))
      → ⦃ _ : True (Omniscient→Exhaustible (ℰ!⇒Omniscient (tup-inst n insts)) (Π[ n ^ expl $] .fun P?)) ⦄
      → xs ⦂⦅ Xs ⦆Π[ expl ]→ P xs)
  ∀↯ⁿ = Π[ n ^ inst $] .inv λ fs P? ⦃ p ⦄ → Π[ n ^ expl $] .inv (toWitness p)
\end{code}
%<*exists-zap-n>
\begin{code}
  ∃↯ⁿ : insts ⦂⦅ map-types ℰ! Xs ⦆Π[ inst ]→
      ( (P? : xs ⦂⦅ Xs ⦆Π[ expl ]→ Dec (P xs))
      → ⦃ _ : True (ℰ!⇒Omniscient (tup-inst n insts) (Π[ n ^ expl $] .fun P?) ) ⦄
      → Σ ⦅ Xs ⦆ P)
  ∃↯ⁿ = Π[ n ^ inst $] .inv (λ fs P? ⦃ p ⦄ → toWitness p)
\end{code}
%</exists-zap-n>
