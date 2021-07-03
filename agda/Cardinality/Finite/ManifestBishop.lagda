\begin{code}
{-# OPTIONS --cubical --safe --postfix-projections #-}

module Cardinality.Finite.ManifestBishop where

open import Prelude hiding (_≃_; isEquiv)

import Cardinality.Finite.ManifestBishop.Inductive as 𝕃
import Cardinality.Finite.ManifestBishop.Container as ℒ

open import Cardinality.Finite.ManifestBishop.Isomorphism

open import Data.Fin

private
  variable
    u : Level
    U : A → Type u

private
 module DisplayBishEquiv {a} {A : Type a} where
  open ℒ
  open import Snippets.Equivalence
  open import Container
  open import Container.List
  open import Data.Sigma.Properties

  open import Relation.Binary.Equivalence.Reasoning (⇔-equiv {a}) public
  ℬ⇔Fin≃ :
\end{code}
%<*bishop-is-equiv-type>
\begin{code}
   ℬ A ⇔ ∃[ n ] (Fin n ≃ A)
\end{code}
%</bishop-is-equiv-type>
\begin{code}
  ℬ⇔Fin≃ =
\end{code}
%<*bishop-is-equiv>
\begin{code}
    ℬ A                                                      ≋⟨⟩
    Σ[ xs ⦂ List A ] ((x : A) → x ∈! xs)                     ≋⟨⟩
    Σ[ xs ⦂ List A ] ((x : A) → isContr (x ∈ xs))            ≋⟨⟩
    Σ[ xs ⦂ List A ] ((x : A) → isContr (fiber (snd xs) x))  ≋⟨⟩
    Σ[ xs ⦂ List A ] isEquiv (snd xs)                        ≋⟨⟩
    Σ[ xs ⦂ ⟦ ℕ , Fin ⟧ A ] isEquiv (snd xs)                 ≋⟨⟩
    Σ[ xs ⦂ Σ[ n ⦂ ℕ ] (Fin n → A) ] isEquiv (snd xs)        ≋⟨ reassoc ⟩
    Σ[ n ⦂ ℕ ] Σ[ f ⦂ (Fin n → A) ] isEquiv f                ≋⟨⟩
    ∃[ n ] (Fin n ≃ A) ∎
\end{code}
%</bishop-is-equiv>
\begin{code}


open import Prelude using (_≃_; isEquiv)

module _ where
  open ℒ
  ℬ⇔Fin≃ : ℬ A ⇔ ∃[ n ] (Fin n ≃ A)
  ℬ⇔Fin≃ .fun ((n , xs) , cov) .fst = n
  ℬ⇔Fin≃ .fun ((n , xs) , cov) .snd .fst = xs
  ℬ⇔Fin≃ .fun ((n , xs) , cov) .snd .snd .equiv-proof = cov
  ℬ⇔Fin≃ .inv (n , (xs , cov)) = ((n , xs) , cov .equiv-proof)
  ℬ⇔Fin≃ .rightInv (n , (xs , cov)) i .fst = n
  ℬ⇔Fin≃ .rightInv (n , (xs , cov)) i .snd .fst = xs
  ℬ⇔Fin≃ .rightInv (n , (xs , cov)) i .snd .snd .equiv-proof = cov .equiv-proof
  ℬ⇔Fin≃ .leftInv _ = refl

module _ where
  open 𝕃

  open import Cardinality.Finite.SplitEnumerable hiding (_|×|_; ℰ!⟨Tuple⟩)
  import Cardinality.Finite.SplitEnumerable as SplitEnumerable
  open import Cardinality.Finite.SplitEnumerable.Inductive
  open import Cardinality.Finite.SplitEnumerable.Isomorphism

  ℬ⇒ℰ! : ℬ A → ℰ! A
  ℬ⇒ℰ! xs .fst = xs .fst
  ℬ⇒ℰ! xs .snd x = xs .snd x .fst

  ℬ⇒Discrete : ℬ A → Discrete A
  ℬ⇒Discrete = ℰ!⇒Discrete ∘ fun 𝕃⇔ℒ⟨ℰ!⟩ ∘ ℬ⇒ℰ!

  module SplitEnumToBishop where
    ℰ!⇒ℬ : ℰ! A → ℬ A
    ℰ!⇒ℬ xs = λ where
        .fst → uniques disc (xs .fst)
        .snd x → ∈⇒∈! disc x (xs .fst) (xs .snd x)
      where
      disc = ℰ!⇒Discrete (𝕃⇔ℒ⟨ℰ!⟩ .fun xs)

  ℬ⇒Fin≃ : ℬ A → ∃[ n ] (Fin n ≃ A)
  ℬ⇒Fin≃ = ℬ⇔Fin≃ .fun ∘ 𝕃⇔ℒ⟨ℬ⟩ .fun

  private
    module PiClosNoPoly {A : Type₀} {U : A → Type₀} where
      open import Data.Tuple.UniverseMonomorphic
      open TupleUniverseMonomorphic
      ℰ!⇒ℬ : ℰ! B → _
      ℰ!⇒ℬ = 𝕃⇔ℒ⟨ℬ⟩ .fun ∘ SplitEnumToBishop.ℰ!⇒ℬ

      _|Π|_ : ℰ! A → ((x : A) → ℰ! (U x)) → ℰ! ((x : A) → U x)
      _|Π|_ xs =
        subst
          (λ t → {A : t → Type _} → ((x : t) → ℰ! (A x)) → ℰ! ((x : t) → (A x)))
          (ua (ℬ⇔Fin≃ .fun (ℰ!⇒ℬ xs) .snd))
          (subst ℰ! (isoToPath Tuple⇔ΠFin) ∘ ℰ!⟨Tuple⟩)

  open SplitEnumToBishop public
  isoLift : Lift b A ⇔ A
  isoLift = iso lower lift (λ _ → refl) λ _ → refl
  open import Data.Tuple

  module _ {a} {u} {A : Type a} {U : A → Type u} where
\end{code}
%<*pi-clos>
\begin{code}
    _|Π|_ : ℰ! A → ((x : A) → ℰ! (U x)) → ℰ! ((x : A) → U x)
\end{code}
%</pi-clos>
\begin{code}
    _|Π|_ xs =
      subst
        (λ t → {A : t → Type _} → ((x : t) → ℰ! (A x)) → ℰ! ((x : t) → (A x)))
        (ua (isoToEquiv isoLift ⟨ trans-≃ ⟩ ℬ⇔Fin≃ .fun (𝕃⇔ℒ⟨ℬ⟩ .fun (ℰ!⇒ℬ xs)) .snd))
        (subst ℰ! (isoToPath (isoLift {b = a} ⟨ trans-⇔ ⟩ Tuple⇔ΠFin)) ∘ ℰ!⟨Lift⟩ ∘ SplitEnumerable.ℰ!⟨Tuple⟩)

  open import HITs.PropositionalTruncation.Sugar

  ℬ⇒Choice : ℬ A → ((x : A) → ∥ U x ∥) → ∥ (∀ x → U x) ∥
  ℬ⇒Choice ba =
    subst
      (λ t → {U : t → Type _} → ((x : t) → ∥ U x ∥) → ∥ ((x : t) → U x) ∥)
      (ua (isoToEquiv isoLift ⟨ trans-≃ ⟩ ℬ⇔Fin≃ .fun (𝕃⇔ℒ⟨ℬ⟩ .fun ba) .snd))
      ((ind ∥$∥_) ∘ trav _ ∘ tab)
    where
    trav : ∀ n {T : Lift a (Fin n) → Type b} → Tuple n (∥_∥ ∘ T) → ∥ Tuple n T ∥
    trav zero    xs = ∣ _ ∣
    trav (suc n) (x , xs) = do
      x′ ← x
      xs′ ← trav n xs
      ∣ x′ , xs′ ∣

  module BishopClosures where
\end{code}
%<*times-clos-sig>
\begin{code}
    _|×|_ :  ℬ A →
             ℬ B →
             ℬ (A × B)
\end{code}
%</times-clos-sig>
\begin{code}
    xs |×| ys = ℰ!⇒ℬ (ℬ⇒ℰ! xs SplitEnumerable.|×| ℬ⇒ℰ! ys)
\end{code}
\begin{code}

    open import Cubical.Foundations.HLevels
    open import Relation.Nullary.Decidable.Logic

    _|→|_ : ℬ A → ℬ B → ℬ (A → B)
    xs |→| ys = ℰ!⇒ℬ (ℬ⇒ℰ! xs |Π| λ _ → ℬ⇒ℰ! ys)

    filter : ∀ {p} {P : A → Type p} → (∀ x → isProp (P x)) → (∀ x → Dec (P x)) → ℬ A → ℬ (Σ[ x ⦂ A ] P x)
    filter isPropP P? = ℰ!⇒ℬ ∘ filter-subobject isPropP P? ∘ ℬ⇒ℰ!

    module _ {a} {b} {A : Type a} {B : Type b} where
\end{code}
%<*iso-finite>
\begin{code}
      iso-finite :  ℬ A →
                    ℬ B →
                    ℬ (Σ[ f,g ⦂ (A → B) × (B → A) ]
                        (  (f,g .fst ∘ f,g .snd ≡ id) ×
                           (f,g .snd ∘ f,g .fst ≡ id)))
      iso-finite ℬ⟨A⟩ ℬ⟨B⟩ =
        filter
          (λ _ → isPropEqs)
          (λ { (f , g) → (f ∘ g) ≟ᴮ id && (g ∘ f) ≟ᴬ id})
          ((ℬ⟨A⟩ |→| ℬ⟨B⟩) |×| (ℬ⟨B⟩ |→| ℬ⟨A⟩))
\end{code}
%</iso-finite>
\begin{code}
        where
        ℬ⟨f⟩ : ℬ (A → B)
        ℬ⟨f⟩ = (ℬ⟨A⟩ |→| ℬ⟨B⟩)

        ℬ⟨g⟩ : ℬ (B → A)
        ℬ⟨g⟩ = (ℬ⟨B⟩ |→| ℬ⟨A⟩)

        _≟ᴮ_ = ℬ⇒Discrete (ℬ⟨B⟩ |→| ℬ⟨B⟩)
        _≟ᴬ_ = ℬ⇒Discrete (ℬ⟨A⟩ |→| ℬ⟨A⟩)

        isPropEqs : {g : A → A} {f : B → B} → isProp ((f ≡ id) × (g ≡ id))
        isPropEqs = isOfHLevelΣ 1 (Discrete→isSet _≟ᴮ_ _ _) λ _ → (Discrete→isSet _≟ᴬ_ _ _)

      _|⇔|_ : ℬ A → ℬ B → ℬ (A ⇔ B)
      xs |⇔| ys = subst ℬ (isoToPath form) (iso-finite xs ys)
        where
        form : (Σ[ fg ⦂ ((A → B) × (B → A)) ] (((fg .fst ∘ fg .snd) ≡ id) × ((fg .snd ∘ fg .fst) ≡ id))) ⇔ (A ⇔ B)
        form .fun ((f , g) , (leftInv , rightInv)) = iso f g (λ x i → leftInv i x) (λ x i → rightInv i x)
        form .inv fg = ((fg .fun , fg .inv) , ((λ i x → fg .rightInv x i) , (λ i x → fg .leftInv x i)))
        form .rightInv fg i .fun = fg .fun
        form .rightInv fg i .inv = fg .inv
        form .rightInv fg i .rightInv = fg .rightInv
        form .rightInv fg i .leftInv = fg .leftInv
        form .leftInv  _ = refl

    private
      module DecTerm (f : A → B) (g : B → A) where
        decTerm : Type _
        decTerm =
\end{code}
%<*dec-type>
\begin{code}
          Dec (f ∘ g ≡ id)
\end{code}
%</dec-type>
