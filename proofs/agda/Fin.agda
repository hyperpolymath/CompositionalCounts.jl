{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- CompositionalCounts.jl — machine-checked algebraic claims.
--
-- Fin : finite indices.  Fin n is the type of natural numbers k
-- strictly below n, encoded existentially over the builtin Σ type
-- (this keeps every type in Set and needs no axioms).
--
-- House style (see Basics): single universe Set; every parameter
-- declared explicitly; every implicit parameter used in a clause
-- body named in the clause head; no forward references.
------------------------------------------------------------------------

module Fin where

open import Basics
open import Nat
open import Agda.Builtin.Nat      using (zero ; suc ; _+_)
open import Agda.Builtin.Bool     using (Bool ; true ; false)
open import Agda.Builtin.Equality using (_≡_ ; refl)
open import Agda.Builtin.Sigma    using (Σ ; fst ; snd ; _,_)
open import Agda.Builtin.Unit     using (⊤ ; tt)

------------------------------------------------------------------------
-- The strict order as a proposition, witnessed by the boolean test:
-- k <p n  :=  _<?>_ k n ≡ true.

_<p_ : ℕ → ℕ → Set
k <p n = _<?>_ k n ≡ true

infix 4 _<p_

------------------------------------------------------------------------
-- The finite type.

Fin : ℕ → Set
Fin n = Σ ℕ (λ k → k <p n)

fromFin : (n : ℕ) → Fin n → ℕ
fromFin n = fst

fzero : (n : ℕ) → Fin (suc n)
fzero n = (zero , refl)

fsuc : (n : ℕ) → Fin n → Fin (suc n)
fsuc n (k , e) = (suc k , e)

-- Fin 0 is empty.

Fin-0-empty : Fin 0 → ⊥
Fin-0-empty (k , e) with k
Fin-0-empty (k , e) | zero with e
Fin-0-empty (k , e) | zero | ()
Fin-0-empty (k , e) | (suc k₁) with e
Fin-0-empty (k , e) | (suc k₁) | ()

-- Every element of Fin n is strictly below n.

fromFin-bounds : (n : ℕ) → (i : Fin n) → fromFin n i <N n
fromFin-bounds n (k , e) = <?-sound {k} {n} e

-- Decidability of equality of indices (via their values).

Fin-eq? : (n : ℕ) → (i j : Fin n) → Dec (fromFin n i ≡ fromFin n j)
Fin-eq? n i j = natEq? (fromFin n i) (fromFin n j)

-- Advancing an index by one, when the result is still in range.
fin-advance : (n : ℕ) → (i : Fin n) → fromFin n i + 1 <N n → Fin n
fin-advance zero (k₀ , e₀) h with k₀
fin-advance zero (k₀ , e₀) h | zero with h
fin-advance zero (k₀ , e₀) h | zero | (j , e) with e
fin-advance zero (k₀ , e₀) h | zero | (j , e) | ()
fin-advance zero (k₀ , e₀) h | (suc k₁) with h
fin-advance zero (k₀ , e₀) h | (suc k₁) | (j , e) with e
fin-advance zero (k₀ , e₀) h | (suc k₁) | (j , e) | ()
fin-advance (suc n) i h =
  (fromFin (suc n) i + 1 , <?-complete (fromFin (suc n) i + 1) (suc n) h)
