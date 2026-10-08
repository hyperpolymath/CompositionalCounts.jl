{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- CompositionalCounts.jl — machine-checked algebraic claims.
--
-- Vec : vectors, encoded as a nested Σ type:
--   Vec A zero  := ⊤
--   Vec A (suc n) := Σ A (λ _ → Vec A n)
-- so every type stays in Set and no axioms are needed.
--
-- House style (see Basics): single universe Set; every parameter
-- declared explicitly; every implicit parameter used in a clause
-- body named in the clause head; no forward references.
------------------------------------------------------------------------

module Vec where

open import Basics
open import Nat
open import Fin
open import Agda.Builtin.Nat      using (zero ; suc)
open import Agda.Builtin.Equality using (_≡_ ; refl)
open import Agda.Builtin.Sigma    using (Σ ; fst ; snd ; _,_)
open import Agda.Builtin.Unit     using (⊤ ; tt)

------------------------------------------------------------------------
-- Vectors.

Vec : Set → ℕ → Set
Vec A zero    = ⊤
Vec A (suc n) = Σ A (λ _ → Vec A n)

vzero : (A : Set) → Vec A 0
vzero A = tt

vsuc : (A : Set) → (a : A) → (n : ℕ) → Vec A n → Vec A (suc n)
vsuc A a n v = (a , v)

vlength : (A : Set) → (n : ℕ) → Vec A n → ℕ
vlength A zero  v = zero
vlength A (suc n) v = suc (vlength A n (snd v))

------------------------------------------------------------------------
-- Lookup by a finite index.

vlookup : (A : Set) → (n : ℕ) → (v : Vec A n) → (i : Fin n) → A
vlookup A zero v i with i
vlookup A zero v i | (k , e₁) with k
vlookup A zero v i | (k , e₁) | zero with e₁
vlookup A zero v i | (k , e₁) | zero | ()
vlookup A zero v i | (k , e₁) | (suc k₁) with e₁
vlookup A zero v i | (k , e₁) | (suc k₁) | ()
vlookup A (suc n) (a , v) i with i
vlookup A (suc n) (a , v) i | (zero , e₁) = a
vlookup A (suc n) (a , v) i | (suc k₁ , e₁) = vlookup A n v (k₁ , e₁)

-- Looking up the first element of a vsuc vector.

vlookup-fzero : (A : Set) → (n : ℕ) → (a : A) → (v : Vec A n) →
  vlookup A (suc n) (vsuc A a n v) (fzero n) ≡ a
vlookup-fzero A n a v = refl

-- Looking up a successor element skips past the head.

vlookup-fsuc : (A : Set) → (n : ℕ) → (a : A) → (v : Vec A n) → (k : Fin n) →
  vlookup A (suc n) (vsuc A a n v) (fsuc n k) ≡ vlookup A n v k
vlookup-fsuc A n a v k = refl

-- Equal indices (as values) give equal lookups.

vlookup-cong : (A : Set) → (n : ℕ) → (v : Vec A n) → (i j : Fin n) →
  fromFin n i ≡ fromFin n j → vlookup A n v i ≡ vlookup A n v j
vlookup-cong A zero v i j e with i
vlookup-cong A zero v i j e | (k , e₁) with k
vlookup-cong A zero v i j e | (k , e₁) | zero with e₁
vlookup-cong A zero v i j e | (k , e₁) | zero | ()
vlookup-cong A zero v i j e | (k , e₁) | (suc k₁) with e₁
vlookup-cong A zero v i j e | (k , e₁) | (suc k₁) | ()
vlookup-cong A (suc n) (a , v) i j e with i
vlookup-cong A (suc n) (a , v) i j e | (zero , e₁) with j
vlookup-cong A (suc n) (a , v) i j e | (zero , e₁) | (zero , e₂) = refl
vlookup-cong A (suc n) (a , v) i j e | (zero , e₁) | (suc k₂ , e₂) with e
vlookup-cong A (suc n) (a , v) i j e | (zero , e₁) | (suc k₂ , e₂) | ()
vlookup-cong A (suc n) (a , v) i j e | (suc k₁ , e₁) with j
vlookup-cong A (suc n) (a , v) i j e | (suc k₁ , e₁) | (zero , e₂) with e
vlookup-cong A (suc n) (a , v) i j e | (suc k₁ , e₁) | (zero , e₂) | ()
vlookup-cong A (suc n) (a , v) i j e | (suc k₁ , e₁) | (suc k₂ , e₂) =
  vlookup-cong A n v (k₁ , e₁) (k₂ , e₂) (suc-inj e)

------------------------------------------------------------------------
-- Construction and mapping.

vmap : (A B : Set) → (n : ℕ) → (f : A → B) → (v : Vec A n) → Vec B n
vmap A B zero  f v       = tt
vmap A B (suc n) f (a , v) = (f a , vmap A B n f v)

vreplicate : (A : Set) → (n : ℕ) → (a : A) → Vec A n
vreplicate A zero  a = tt
vreplicate A (suc n) a = (a , vreplicate A n a)

-- Looking up a constant vector returns the constant.

vlookup-replicate : (A : Set) → (n : ℕ) → (a : A) → (i : Fin n) →
  vlookup A n (vreplicate A n a) i ≡ a
vlookup-replicate A zero a i with i
vlookup-replicate A zero a i | (k , e₁) with k
vlookup-replicate A zero a i | (k , e₁) | zero with e₁
vlookup-replicate A zero a i | (k , e₁) | zero | ()
vlookup-replicate A zero a i | (k , e₁) | (suc k₁) with e₁
vlookup-replicate A zero a i | (k , e₁) | (suc k₁) | ()
vlookup-replicate A (suc n) a i with i
vlookup-replicate A (suc n) a i | (zero , e₁) = refl
vlookup-replicate A (suc n) a i | (suc k₁ , e₁) =
  vlookup-replicate A n a (k₁ , e₁)

------------------------------------------------------------------------
-- Extensionality: a vector is determined by its lookups.

-- Pair congruence for the vec-Σ (the fibre ignores the head).

vec-eq-const : (A : Set) → (n : ℕ) → {a1 a2 : A} → {v1 v2 : Vec A n} →
  a1 ≡ a2 → v1 ≡ v2 → (a1 , v1) ≡ (a2 , v2)
vec-eq-const A n {a1} {a2} {v1} {v2} e1 e2 =
  trans (cong (λ x → x , v1) e1) (cong (λ y → a2 , y) e2)

vec-ext : (A : Set) → (n : ℕ) → (v w : Vec A n) →
  (∀ (i : Fin n) → vlookup A n v i ≡ vlookup A n w i) → v ≡ w
vec-ext A zero v w p = refl
vec-ext A (suc n) (a , v) (b , w) p =
  vec-eq-const A n (p (fzero n))
    (vec-ext A n v w
       (λ i → trans (vlookup-fsuc A n a v i)
                    (trans (p (fsuc n i))
                           (sym (vlookup-fsuc A n b w i)))))

-- Pointwise mapping, at the lookup level.
vlookup-vmap : (A B : Set) → (n : ℕ) → (g : A → B) → (v : Vec A n) →
  (k : Fin n) →
  vlookup B n (vmap A B n g v) k ≡ g (vlookup A n v k)
vlookup-vmap A B zero g v i with i
vlookup-vmap A B zero g v i | (k₀ , e) with k₀
vlookup-vmap A B zero g v i | (k₀ , e) | zero with e
vlookup-vmap A B zero g v i | (k₀ , e) | zero | ()
vlookup-vmap A B zero g v i | (k₀ , e) | (suc k₁) with e
vlookup-vmap A B zero g v i | (k₀ , e) | (suc k₁) | ()
vlookup-vmap A B (suc n) g (a , v) k with k
vlookup-vmap A B (suc n) g (a , v) k | (zero , e₀) = refl
vlookup-vmap A B (suc n) g (a , v) k | (suc k₁ , e₀) =
  vlookup-vmap A B n g v (k₁ , e₀)
