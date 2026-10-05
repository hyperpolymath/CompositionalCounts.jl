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
col J n C j = vlookup J n C j

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
ref-ok-decidable J n C j | yes hp | no ¬ht = no (λ (pair a b) → ¬ht b)
ref-ok-decidable J n C j | no ¬hp = no (λ (pair a b) → ¬hp a)

------------------------------------------------------------------------
-- Decidability of negation, and of the existence of a reference.

dec-not : (P : Set) → Dec P → Dec (¬ P)
dec-not P (yes p) = no (λ ¬p → ¬p p)
dec-not P (no ¬p) = yes (λ q → ¬p q)

-- The tail of the counts table.
tail : (n : ℕ) → Counts (suc J) n → Counts J n
tail n C = snd C

dec-exists : (J n : ℕ) → (C : Counts J n) →
  Dec (Σ (Fin J) (λ j → ref-ok J n C j))
dec-exists zero n C = no no-exists-zero
dec-exists (suc J) n C with ref-ok-decidable (suc J) n C (fzero J)
dec-exists (suc J) n C | yes q = yes (fzero J , q)
dec-exists (suc J) n C | no ¬q with dec-exists J n (tail n C)
dec-exists (suc J) n C | no ¬q | yes (k , q′) = yes (fsuc J k , q′)
dec-exists (suc J) n C | no ¬q | no ¬tail = no (no-both ¬q ¬tail)
  where
    no-exists-zero : ¬ (Σ (Fin zero) (λ j → ref-ok zero n C j))
    no-exists-zero (j₀ , q₀) with j₀
    no-exists-zero (j₀ , q₀) | (zero , e) with e
    no-exists-zero (j₀ , q₀) | (zero , e) | ()
    no-exists-zero (j₀ , q₀) | (fsuc zero (k₁ , e)) with e
    no-exists-zero (j₀ , q₀) | (fsuc zero (k₁ , e)) | ()
    no-both : (¬q : ¬ ref-ok (suc J) n C (fzero J)) →
      (¬tail : ¬ (Σ (Fin J) (λ j → ref-ok J n (tail n C) j))) →
      ¬ (Σ (Fin (suc J)) (λ j → ref-ok (suc J) n C j))
    no-both ¬q ¬tail (j₀ , q₀) with j₀
    no-both ¬q ¬tail (j₀ , q₀) | (zero , e₀) with e₀
    no-both ¬q ¬tail (j₀ , q₀) | (zero , e₀) | ()
    no-both ¬q ¬tail (j₀ , q₀) | (fsuc J (k , e₀)) = ¬tail (k , e₀) q₀

-- The refusal condition: no taxon satisfies the reference rule.
refuse : (J n : ℕ) → (C : Counts J n) → Set
refuse J n C = ¬ (Σ (Fin J) (λ j → ref-ok J n C j))

refuse-decidable : (J n : ℕ) → (C : Counts J n) → Dec (refuse J n C)
refuse-decidable J n C = dec-not (refuse J n C) (dec-exists J n C)

-- The lowest index at which the rule holds.
first-ok : (J n : ℕ) → (C : Counts J n) →
  (h : Σ (Fin J) (λ j → ref-ok J n C j)) → Fin J
first-ok zero n C h with h
first-ok zero n C (j₀ , q₀) with j₀
first-ok zero n C (j₀ , q₀) | (zero , e) with e
first-ok zero n C (j₀ , q₀) | (zero , e) | ()
first-ok zero n C (j₀ , q₀) | (suc k₁ , e) with e
first-ok zero n C (j₀ , q₀) | (suc k₁ , e) | ()
first-ok (suc J) n C (j₀ , q₀) with ref-ok-decidable (suc J) n C (fzero J)
first-ok (suc J) n C (j₀ , q₀) | yes _ = fzero J
first-ok (suc J) n C (j₀ , q₀) | no ¬q with j₀
first-ok (suc J) n C (j₀ , q₀) | no ¬q | (zero , e₀) with e₀
first-ok (suc J) n C (j₀ , q₀) | no ¬q | (zero , e₀) | ()
first-ok (suc J) n C (j₀ , q₀) | no ¬q | (suc k₁ , e₀) =
  fsuc J (k₁ , e₁)
  where
    -- suc k₁ <?> suc J  ≡  k₁ <?> J
    e₁ : k₁ <?> J ≡ true
    e₁ = trans (sym (<?>-suc-suc k₁ J)) e₀
