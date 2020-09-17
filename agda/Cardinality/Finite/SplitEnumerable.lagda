\begin{code}
{-# OPTIONS --cubical --safe --postfix-projections #-}

module Cardinality.Finite.SplitEnumerable where

open import Prelude
open import Container
open import Data.Fin
open import Data.Sigma.Properties
open import Function.Surjective.Properties
open import Data.Fin.Properties

import Cardinality.Finite.SplitEnumerable.Container as ℒ
import Cardinality.Finite.SplitEnumerable.Inductive as 𝕃
open import Cardinality.Finite.SplitEnumerable.Isomorphism

open import Data.Nat.Literals
open import Data.Fin.Literals
open import Literals.Number

private
  variable
    u : Level
    U : A → Type u

module _ {a} {A : Type a} where
 open ℒ
 open import Container.List
 open import Container.Membership (ℕ , Fin)
 open import Relation.Binary.Equivalence.Reasoning (⇔-equiv {a})

\end{code}
%<*split-enum-is-split-surj-short>
\begin{code}
 split-enum-is-split-surj : ℰ! A ⇔ Σ[ n ⦂ ℕ ] (Fin n ↠! A)
 split-enum-is-split-surj = reassoc
\end{code}
%</split-enum-is-split-surj-short>
\begin{code}

 ℰ!⇔Fin↠! :
\end{code}
%<*is-split-inj-type>
\begin{code}
   ℰ! A ⇔ Σ[ n ⦂ ℕ ] (Fin n ↠! A)
\end{code}
%</is-split-inj-type>
\begin{code}
 ℰ!⇔Fin↠! =
\end{code}
%<*is-split-inj>
\begin{code}
   ℰ! A                                                       ≋⟨⟩
   Σ[ xs ⦂ List A ] ((x : A) → x ∈ xs)                        ≋⟨⟩
   Σ[ xs ⦂ List A ] ((x : A) → fiber (snd xs) x)              ≋⟨⟩
   Σ[ xs ⦂ List A ] SplitSurjective (snd xs)                  ≋⟨⟩
   Σ[ xs ⦂ ⟦ ℕ , Fin ⟧ A ] SplitSurjective (snd xs)           ≋⟨⟩
   Σ[ xs ⦂ Σ[ n ⦂ ℕ ] (Fin n → A) ] SplitSurjective (snd xs)  ≋⟨ reassoc ⟩
   Σ[ n ⦂ ℕ ] Σ[ f ⦂ (Fin n → A) ] SplitSurjective f          ≋⟨⟩
   Σ[ n ⦂ ℕ ] (Fin n ↠! A) ∎
\end{code}
%</is-split-inj>
%<*split-is-discrete>
\begin{code}
 ℰ!⇒Discrete : ℰ! A → Discrete A
 ℰ!⇒Discrete  = flip Discrete-distrib-surj discreteFin
              ∘ snd
              ∘ ℰ!⇔Fin↠! .fun
\end{code}
%</split-is-discrete>
\begin{code}
module _ where
 open 𝕃
 open import Data.List.Sugar hiding ([_])
 open import Data.List.Syntax
 open import Data.List.Membership

 module BoolSlop where
\end{code}
%<*bool-slop>
\begin{code}
   ℰ!⟨2⟩ : ℰ! Bool
   ℰ!⟨2⟩ .fst = [ false , true , false ]
   ℰ!⟨2⟩ .snd false  = 0  , refl
   ℰ!⟨2⟩ .snd true   = 1  , refl
\end{code}
%</bool-slop>
\begin{code}
\end{code}
%<*bool-rev>
\begin{code}
 ℰ!⟨2⟩′ : ℰ! Bool
 ℰ!⟨2⟩′ .fst = [ true , false ]
 ℰ!⟨2⟩′ .snd false  = 1  , refl
 ℰ!⟨2⟩′ .snd true   = 0  , refl
\end{code}
%</bool-rev>
%<*bool-inst>
\begin{code}
 ℰ!⟨2⟩ : ℰ! Bool
 ℰ!⟨2⟩ .fst = [ false , true ]
 ℰ!⟨2⟩ .snd false  = 0  , refl
 ℰ!⟨2⟩ .snd true   = 1  , refl
\end{code}
%</bool-inst>
%<*top-bot-inst>
\begin{code}
 ℰ!⟨⊤⟩ : ℰ! ⊤
 ℰ!⟨⊤⟩ .fst = [ tt ]
 ℰ!⟨⊤⟩ .snd _ = 0 , refl

 ℰ!⟨⊥⟩ : ℰ! ⊥
 ℰ!⟨⊥⟩ = [] , λ ()
\end{code}
%</top-bot-inst>
%<*sup-sigma>
\begin{code}
 sup-Σ :  List A →
          ((x : A) → List (U x)) →
          List (Σ A U)
 sup-Σ xs ys = do  x ← xs
                   y ← ys x
                   [ x , y ]
\end{code}
%</sup-sigma>
\begin{code}
 cov-Σ : (x : A)
       → (y : U x)
       → (xs : List A)
       → (ys : ∀ x → List (U x))
       → x ∈ xs
       → y ∈ ys x
       → (x , y) ∈ sup-Σ xs ys
 cov-Σ xᵢ yᵢ (x ∷ xs) ys (fs n , x∈xs) y∈ys =
   map (x ,_) (ys x) ++◇ cov-Σ xᵢ yᵢ xs ys (n , x∈xs) y∈ys
 cov-Σ xᵢ yᵢ (x ∷ xs) ys (f0  , x∈xs) y∈ys =
   subst (λ x′ → (xᵢ , yᵢ) ∈ sup-Σ (x′ ∷ xs) ys) (sym x∈xs)
   (map (xᵢ ,_) (ys xᵢ) ◇++ cong-∈ (xᵢ ,_) (ys xᵢ) y∈ys)
\end{code}
%<*split-enum-sigma>
\begin{code}
 _|Σ|_ : ℰ! A → (∀ x → ℰ! (U x)) → ℰ! (Σ A U)
\end{code}
%</split-enum-sigma>
\begin{code}
 (xs |Σ| ys) .fst = sup-Σ (xs .fst) (fst ∘ ys)
 (xs |Σ| ys) .snd (x , y) = cov-Σ x y (xs .fst) (fst ∘ ys) (xs .snd x) (ys x .snd y)

 ℰ!⟨Fin⟩ : ∀ {n} → ℰ! (Fin n)
 ℰ!⟨Fin⟩ .fst = tabulate _ id
 ℰ!⟨Fin⟩ .snd = fin∈tabulate id

 _|×|_ : ℰ! A → ℰ! B → ℰ! (A × B)
 xs |×| ys = xs |Σ| const ys

 _|⊎|_ : ℰ! A → ℰ! B → ℰ! (A ⊎ B)
 (xs |⊎| ys) .fst = map inl (xs .fst) ++ map inr (ys .fst)
 (xs |⊎| ys) .snd (inl x) = map inl (xs .fst) ◇++ cong-∈ inl (xs .fst) (xs .snd x)
 (xs |⊎| ys) .snd (inr y) = map inl (xs .fst) ++◇ cong-∈ inr (ys .fst) (ys .snd y)

 _|+|_ : ℰ! A → ℰ! B → ℰ! (Σ[ t ⦂ Bool ] (if t then A else B))
 xs |+| ys = ℰ!⟨2⟩ |Σ| bool ys xs

 module TupleUniverseMonomorphic where
   open import Data.Tuple.UniverseMonomorphic

   ℰ!⟨Tuple⟩ : ∀ {n} {U : Fin n → Type₀} → (∀ i → ℰ! (U i)) → ℰ! (Tuple n U)
   ℰ!⟨Tuple⟩ {n = zero}  f = (_ ∷ []) , λ _ → f0 , refl
   ℰ!⟨Tuple⟩ {n = suc n} f = f f0 |×| ℰ!⟨Tuple⟩ (f ∘ fs)

 open import Data.Tuple

 ℰ!⟨Tuple⟩ : ∀ {n u} {U : Lift a (Fin n) → Type u} → (∀ i → ℰ! (U i)) → ℰ! (Tuple n U)
 ℰ!⟨Tuple⟩ {n = zero}  f = (_ ∷ []) , λ _ → f0 , refl
 ℰ!⟨Tuple⟩ {n = suc n} f = f (lift f0) |×| ℰ!⟨Tuple⟩ (f ∘ lift ∘ fs ∘ lower)

 ℰ!⟨Lift⟩ : ℰ! A → ℰ! (Lift b A)
 ℰ!⟨Lift⟩ xs .fst = map lift (xs .fst)
 ℰ!⟨Lift⟩ xs .snd x = cong-∈ lift (xs .fst) (xs .snd (x .lower))

 ℰ!⟨≡⟩ : (x y : A) → ℰ! A → ℰ! (x ≡ y)
 ℰ!⟨≡⟩ x y e with ℰ!⇒Discrete (𝕃⇔ℒ⟨ℰ!⟩ .fun e) x y
 ℰ!⟨≡⟩ x y e | yes p = (p ∷ []) , λ q → (f0 , Discrete→isSet (ℰ!⇒Discrete (𝕃⇔ℒ⟨ℰ!⟩ .fun e)) x y p q)
 ℰ!⟨≡⟩ x y e | no ¬p = [] , (⊥-elim ∘ ¬p)

 open import Data.List.Filter
 open import Cardinality.Finite.SplitEnumerable.Inductive

 module _ {p} {P : A → Type p} where

\end{code}
%<*subobject>
\begin{code}
  filter-subobject :
    (∀ x → isProp (P x)) →
    (∀ x → Dec (P x)) →
    ℰ! A →
    ℰ! (Σ[ x ⦂ A ] P x)
\end{code}
%</subobject>
\begin{code}
  filter-subobject isPropP P? xs .fst = filter P? (xs .fst)
  filter-subobject isPropP P? xs .snd (x , v) = filter-preserves isPropP P? (xs .fst) x v (xs .snd x)
\end{code}
