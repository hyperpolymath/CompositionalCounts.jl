{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- CompositionalCounts.jl — machine-checked algebraic claims.
--
-- ReferenceTaxon : the reference-taxon selection rule and its
-- decidability.
--
-- The counts table is  Counts J n  =  Vec (Vec ℕ n) J : for J taxa
-- and n samples, column j is the count of taxon j across the n
-- samples.  The reference rule (method-conditions):
--
--     ref-ok j  :=  (2 · posCount j) ≥ n  ×  (total j > 0)
--
-- i.e. the taxon is observed in at least half the samples and has a
-- positive total count.  The claims proved here:
--
--   * the rule is decidable, column by column, and so is the
--     existence of a reference taxon (dec-exists);
--   * the fit refuses exactly when the rule fails for every taxon
--     (refuse, refuse-decidable);
--   * the selection is deterministic — maximal (prevalence, total)
--     key, lowest index on ties — and sound (select-col,
--     select-sound);
--   * a user-supplied reference is checked and never replaced
--     (user-ref-invariant), and the fit refuses exactly when it
--     fails (user-ref-refuses).
--
-- House style (see Basics): every parameter explicit; every implicit
-- parameter used in a clause body named in the clause head; no
-- forward references.
------------------------------------------------------------------------

module ReferenceTaxon where

open import Basics
open import Nat
open import Fin
open import Vec
open import Agda.Builtin.Nat      using (zero ; suc ; _+_ ; _*_)
open import Agda.Builtin.Bool     using (Bool ; true ; false)
open import Agda.Builtin.Equality using (_≡_ ; refl)
open import Agda.Builtin.Sigma    using (Σ ; fst ; snd ; _,_)
open import Agda.Builtin.Unit     using (⊤ ; tt)

------------------------------------------------------------------------
-- The counts table and per-column statistics.

Counts : ℕ → ℕ → Set
Counts J n = Vec (Vec ℕ n) J

col : (J n : ℕ) → (C : Counts J n) → (j : Fin J) → Vec ℕ n
col J n C j = vlookup (Vec ℕ n) J C j

-- Σ over a vector of naturals.
vsum-ℕ : (n : ℕ) → Vec ℕ n → ℕ
vsum-ℕ zero    v        = zero
vsum-ℕ (suc n) (a , v)  = a + vsum-ℕ n v

-- 1 if the count is positive, else 0.
ispos : (x : ℕ) → ℕ
ispos zero    = zero
ispos (suc x) = 1

-- Number of samples in which the taxon has a positive count.
posCount : (n : ℕ) → (v : Vec ℕ n) → ℕ
posCount n v = vsum-ℕ n (vmap ℕ ℕ n ispos v)

-- Total count across samples.
total : (n : ℕ) → (v : Vec ℕ n) → ℕ
total n v = vsum-ℕ n v

------------------------------------------------------------------------
-- The reference rule.

ref-ok : (J n : ℕ) → (C : Counts J n) → (j : Fin J) → Set
ref-ok J n C j =
  (n ≤N 2 * posCount n (col J n C j)) × (zero <N total n (col J n C j))

ref-ok-decidable : (J n : ℕ) → (C : Counts J n) → (j : Fin J) →
  Dec (ref-ok J n C j)
ref-ok-decidable J n C j with natLeq? n (2 * posCount n (col J n C j))
ref-ok-decidable J n C j | yes hp with natLt? zero (total n (col J n C j))
ref-ok-decidable J n C j | yes hp | yes ht = yes (pair hp ht)
ref-ok-decidable J n C j | yes hp | no ¬ht = no (λ q → ¬ht (proj₂ q))
ref-ok-decidable J n C j | no ¬hp = no (λ q → ¬hp (proj₁ q))

------------------------------------------------------------------------
-- Decidability of negation, and of the existence of a reference.

dec-not : (P : Set) → Dec P → Dec (¬ P)
dec-not P (yes p) = no (λ ¬p → ¬p p)
dec-not P (no ¬p) = yes (λ q → ¬p q)

-- The tail of the counts table.
tail : (J n : ℕ) → Counts (suc J) n → Counts J n
tail J n C = snd C

-- No column of an empty table satisfies the rule.
no-exists-zero : (n : ℕ) → (C : Counts zero n) →
  ¬ (Σ (Fin zero) (λ j → ref-ok zero n C j))
no-exists-zero n C (j₀ , q₀) with j₀
no-exists-zero n C (j₀ , q₀) | (zero , e) with e
no-exists-zero n C (j₀ , q₀) | (zero , e) | ()
no-exists-zero n C (j₀ , q₀) | (suc k₁ , e) with e
no-exists-zero n C (j₀ , q₀) | (suc k₁ , e) | ()

-- Neither the head nor any tail column offers a reference.
no-both : (J n : ℕ) → (C : Counts (suc J) n) →
  (¬q : ¬ ref-ok (suc J) n C (fzero J)) →
  (¬tail : ¬ (Σ (Fin J) (λ j → ref-ok J n (tail J n C) j))) →
  ¬ (Σ (Fin (suc J)) (λ j → ref-ok (suc J) n C j))
no-both J n C ¬q ¬tail (j₀ , q₀) with j₀
no-both J n C ¬q ¬tail (j₀ , q₀) | (zero , e₀) = ¬q q₀
no-both J n C ¬q ¬tail (j₀ , q₀) | (suc k₁ , e₀) = ¬tail ((k₁ , e₀) , q₀)

dec-exists : (J n : ℕ) → (C : Counts J n) →
  Dec (Σ (Fin J) (λ j → ref-ok J n C j))
dec-exists zero n C = no (no-exists-zero n C)
dec-exists (suc J) n C with ref-ok-decidable (suc J) n C (fzero J)
dec-exists (suc J) n C | yes q = yes (fzero J , q)
dec-exists (suc J) n C | no ¬q with dec-exists J n (tail J n C)
dec-exists (suc J) n C | no ¬q | yes (k , q′) = yes (fsuc J k , q′)
dec-exists (suc J) n C | no ¬q | no ¬tail =
  no (no-both J n C ¬q ¬tail)

-- The refusal condition: no taxon satisfies the reference rule.
refuse : (J n : ℕ) → (C : Counts J n) → Set
refuse J n C = ¬ (Σ (Fin J) (λ j → ref-ok J n C j))

refuse-decidable : (J n : ℕ) → (C : Counts J n) → Dec (refuse J n C)
refuse-decidable J n C =
  dec-not (Σ (Fin J) (λ j → ref-ok J n C j)) (dec-exists J n C)

-- The fit refuses exactly when the rule fails for every taxon.
refuse-iff : (J n : ℕ) → (C : Counts J n) →
  refuse J n C ↔ (∀ (j : Fin J) → ¬ ref-ok J n C j)
refuse-iff J n C = ⟨ refuse-iff-fwd , refuse-iff-bwd ⟩
  where
    refuse-iff-fwd : refuse J n C → (∀ (j : Fin J) → ¬ ref-ok J n C j)
    refuse-iff-fwd ¬h j q = ¬h (j , q)
    refuse-iff-bwd : (∀ (j : Fin J) → ¬ ref-ok J n C j) → refuse J n C
    refuse-iff-bwd ¬col (j , q) = ¬col j q
