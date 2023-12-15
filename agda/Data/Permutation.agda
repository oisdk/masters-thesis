module Data.Permutation where

open import Prelude
open import Data.Fin
open import Data.Fin.Properties renaming (discreteFin to _≟_)
open import Data.Nat
open import Data.Bool.Properties using (isPropT; T?)

Perm : ℕ → Type₀
Perm zero    = ⊤
Perm (suc n) = Fin (suc n) × Perm n

private variable n m : ℕ

push : Fin (suc n) → Fin n → Fin (suc n)
push f0 = fs
push {n = suc _} (fs i) f0     = f0
push {n = suc _} (fs i) (fs j) = fs (push i j)

index : Perm n → Fin n → Fin n
index {n = suc n} (x , xs) f0 = x
index {n = suc n} (x , xs) (fs i) = push x (index xs i)

push∘shift : ∀ (x y : Fin (suc n)) → (p : x ≢ᶠ y) → push x (shift x y p) ≡ y
push∘shift f0 (fs x) _ = refl
push∘shift {n = suc _} (fs x) f0 _ = refl
push∘shift {n = suc _} (fs x) (fs y) p = cong fs (push∘shift x y p)

shift≢push : ∀ (x : Fin (suc n)) y → x ≢ᶠ push x y
shift≢push f0 y = tt
shift≢push {n = suc _} (fs x) f0 = tt
shift≢push {n = suc _} (fs x) (fs y) = shift≢push x y

shift∘push : ∀ (x : Fin (suc n)) y → shift x (push x y) (shift≢push x y) ≡ y
shift∘push f0 y = refl
shift∘push {n = suc _} (fs x) f0 = refl
shift∘push {n = suc _} (fs x) (fs y) = cong fs (shift∘push x y)

tabulate : (n F↣ n) → Perm n
tabulate {zero}  _ = tt
tabulate {suc n} f = f .fst f0 , tabulate (shrink f)

open import Path.Reasoning

index∘tabulate : ∀ n (f : n F↣ n) i → index (tabulate f) i ≡ f .fst i
index∘tabulate (suc n) f f0     = refl
index∘tabulate (suc n) f (fs i) =
  push (f .fst f0) (index (tabulate (shrink f)) i) ≡⟨ cong (push (f .fst f0)) (index∘tabulate n _ _) ⟩
  push (f .fst f0) (shift (f .fst f0) (f .fst (fs i)) (f .snd tt)) ≡⟨ push∘shift (f .fst f0) (f .fst (fs i)) (f .snd tt) ⟩
  f .fst (fs i) ∎

push-inj : ∀ (x : Fin (suc n)) y z → y ≢ᶠ z → push x y ≢ᶠ push x z
push-inj f0 y z p = p
push-inj {n = suc _} (fs x) f0 (fs x₁) p = tt
push-inj {n = suc _} (fs x) (fs x₁) f0 p = tt
push-inj {n = suc _} (fs x) (fs y) (fs z) p = push-inj x y z p

≢ᶠ-sym : (x y : Fin n) → x ≢ᶠ y → y ≢ᶠ x
≢ᶠ-sym {n = suc _} f0 (fs x) p = tt
≢ᶠ-sym {n = suc _} (fs x) f0 p = tt
≢ᶠ-sym {n = suc _} (fs x) (fs y) p = ≢ᶠ-sym x y p

index-inj : (xs : Perm n) → FInjection (index xs)
index-inj {n = zero} tt {()} p
index-inj {n = suc n} xs {f0} {fs x} p = shift≢push (xs .fst) _
index-inj {n = suc n} xs {fs x} {f0} p = ≢ᶠ-sym (xs .fst) (push (xs .fst) (index (xs .snd) x)) (shift≢push (xs .fst) _)
index-inj {n = suc n} (x , xs) {fs i} {fs j} p = push-inj x _ _ (index-inj xs p)

open import Cubical.Foundations.Everything using (isPropImplicitΠ; isProp→)

isProp-inj : (f : Fin n → Fin n) → isProp (FInjection f)
isProp-inj f = isPropImplicitΠ λ _ → isPropImplicitΠ λ _ → isProp→ (isPropT _)

tabulate∘index : ∀ n (xs : Perm n) → tabulate (index xs , index-inj xs) ≡ xs
tabulate∘index zero    xs       = refl
tabulate∘index (suc n) (x , xs) =
  cong (x ,_) (cong tabulate (Σ≡Prop isProp-inj (funExt λ i → shift∘push x (index xs i))) ; tabulate∘index n xs) 

_≢?_ : (x y : Fin n) → Dec (x ≢ᶠ y)
x ≢? y = T? (not (does (x ≟ y)))

find : Perm n → Fin n → Fin n
find {n = suc _} (x , xs) y with x ≢? y
... | no  x≡y = f0
... | yes x≢y = fs (find xs (shift x y x≢y))

¬x≢x : (x : Fin n) → ¬ (x ≢ᶠ x)
¬x≢x x x≢x with x ≟ x
... | yes p = x≢x
... | no ¬p = ¬p refl

find∘ind : ∀ (xs : Perm n) i → find xs (index xs i) ≡ i
find∘ind {n = suc _} (x , xs) f0 with x ≢? x
... | yes x≢x = ⊥-elim (¬x≢x x x≢x)
... | no  res = refl
find∘ind {n = suc _} (x , xs) (fs y) with x ≢? push x (index xs y)
... | no  x≡ = ⊥-elim (x≡ (shift≢push  x (index xs y)))
... | yes x≢ = cong fs (cong (find xs) (cong (shift x _) (isPropT _ _ _) ; shift∘push x (index xs y)) ; find∘ind xs y)

¬x≢y→x≡y : (x y : Fin n) → ¬ (x ≢ᶠ y) → x ≡ y
¬x≢y→x≡y x y ¬x≢y with x ≟ y 
... | yes p = p
... | no ¬p = ⊥-elim (¬x≢y tt)

ind∘find : ∀ (p : Perm n) i → index p (find p i) ≡ i
ind∘find {n = suc _} (p , ps) i with p  ≢? i
... | yes p≢i = cong (push p) (ind∘find ps _) ; push∘shift p i p≢i
... | no  p≡i = ¬x≢y→x≡y p i p≡i

≢→≢ᶠ : (x y : Fin n) → x ≢ y → x ≢ᶠ y
≢→≢ᶠ x y x≢y with x ≟ y
... | yes p = x≢y p
... | no ¬p = tt

≡→≡ᶠ :  (x y : Fin n) → x ≡ y → ¬ (x ≢ᶠ y)
≡→≡ᶠ x y x≡y p with x ≟ y
≡→≡ᶠ x y x≡y p | no ¬q = ¬q x≡y

⇔→F↣ : (i : Fin n ⇔ Fin n) → FInjection (i .fun)
⇔→F↣ i {x} {y} p = ≢→≢ᶠ (i .fun x) (i .fun y)
  λ fx≡fy → ≡→≡ᶠ x y (sym (i .leftInv x) ; cong (i .inv) fx≡fy ; i .leftInv y) p

Perm⇔ : ∀ n → Perm n ⇔ (Fin n ⇔ Fin n)
Perm⇔ n .fun p .fun = index p
Perm⇔ n .fun p .inv = find p
Perm⇔ n .fun p .rightInv = ind∘find p
Perm⇔ n .fun p .leftInv = find∘ind p
Perm⇔ n .inv i = tabulate (i .fun , ⇔→F↣ i)
Perm⇔ n .rightInv i = iso-fun-inj isSetFin _ _ (funExt (index∘tabulate n (i .fun , ⇔→F↣ i)))
Perm⇔ n .leftInv  p = cong tabulate (Σ≡Prop isProp-inj refl) ; tabulate∘index n p
