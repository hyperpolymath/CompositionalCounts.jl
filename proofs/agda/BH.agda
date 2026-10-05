{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- CompositionalCounts.jl — machine-checked algebraic claims.
--
-- BH : the Benjamini–Hochberg q-value thresholds and the step-up
-- selection rule.
--
-- With m tested effects and FDR level q, the threshold for the
-- (i+1)-st smallest p-value (0-indexed rank i) is
--
--     thr(i)  =  (i+1)/m · q
--
-- and the claims proved here:
--
--   * the thresholds are non-negative and monotone non-decreasing in
--     the rank (BH monotonicity);
--   * the step-up rule — take the largest rank k whose p-value is
--     below its own threshold, and reject every rank up to and
--     including k — rejects exactly the prefix of ranks up to k,
--     and every rejected p-value lies below the common cutoff
--     thr(k) (BH step-up correctness).
--
-- House style (see Basics): every parameter explicit; every implicit
-- parameter used in a clause body named in the clause head; no
-- forward references.
------------------------------------------------------------------------

module BH where

open import Basics
open import Nat
open import Fin
open import Vec
open import Field
open import Agda.Builtin.Nat      using (zero ; suc ; _+_ ; _*_)
open import Agda.Builtin.Bool     using (Bool ; true ; false)
open import Agda.Builtin.Equality using (_≡_ ; refl)
open import Agda.Builtin.Sigma    using (Σ ; fst ; snd ; _,_)
open import Agda.Builtin.Unit     using (⊤ ; tt)

------------------------------------------------------------------------
-- The threshold.

-- thr m q (rank i)  =  (i+1) · q · m⁻¹
bh-threshold : (F : Set) → (f : Field F) → (m : ℕ) → (q : F) →
  (i : Fin m) → F
bh-threshold F f m q i =
  Field.fmul f (Field.fmul f (natToField F f (suc (fromFin m i))) q)
               (Field.finv f (natToField F f m))

------------------------------------------------------------------------
-- Monotonicity in the rank.

bh-threshold-monotone : (F : Set) → (f : Field F) → (o : Ordered F f) →
  (m : ℕ) → (q : F) → (i₁ i₂ : Fin m) →
  fromFin m i₁ ≤N fromFin m i₂ →
  Ordered.le o (Field.fzero f) q →
  natToField F f m ≢ Field.fzero f →
  Ordered.le o
    (bh-threshold F f m q i₁) (bh-threshold F f m q i₂)
bh-threshold-monotone F f o m q i₁ i₂ h hq hNE =
  mul-mono
    (Field.fmul f (natToField F f (suc (fromFin m i₁))) q)
    (Field.fmul f (natToField F f (suc (fromFin m i₂))) q)
    (Field.finv f (natToField F f m))
    (mul-mono (natToField F f (suc (fromFin m i₁)))
              (natToField F f (suc (fromFin m i₂)))
              q
              (nat-embed-mono (suc (fromFin m i₁)) (suc (fromFin m i₂))
                              (suc-lift h))
              hq)
    (inv-pos (natToField F f m) hNE (zero-nat F f o m))
  where
    open Ordered o
      using (le ; le-refl ; le-trans ; le-total ; le-rewrite ;
             le-rewrite-r ; add-mono ; mul-mono ; nat-embed-mono ;
             zero-≤-one ; inv-pos)

------------------------------------------------------------------------
-- The thresholds are non-negative (for a non-negative q).

bh-threshold-nonneg : (F : Set) → (f : Field F) → (o : Ordered F f) →
  (m : ℕ) → (q : F) → (i : Fin m) →
  Ordered.le o (Field.fzero f) q →
  natToField F f m ≢ Field.fzero f →
  Ordered.le o (Field.fzero f) (bh-threshold F f m q i)
bh-threshold-nonneg F f o m q i hq hNE = s4
  where
    open Ordered o
      using (le ; le-refl ; le-trans ; le-total ; le-rewrite ;
             le-rewrite-r ; add-mono ; mul-mono ; nat-embed-mono ;
             zero-≤-one ; inv-pos)
    A : F
    A = Field.fmul f (natToField F f (suc (fromFin m i))) q
    C : F
    C = Field.finv f (natToField F f m)
    -- 0 ≤ (i+1)·q
    s1 : le (Field.fzero f) A
    s1 =
      le-rewrite
        (Field.fmul f (Field.fzero f) q)
        (Field.fzero f)
        A
        (zero-mul F f q)
        (mul-mono (Field.fzero f) (natToField F f (suc (fromFin m i))) q
                  (zero-nat F f o (suc (fromFin m i)))
                  hq)
    -- 0 ≤ m⁻¹
    s2 : le (Field.fzero f) C
    s2 = inv-pos (natToField F f m) hNE (zero-nat F f o m)
    -- 0·C ≤ A·C
    s3 : le (Field.fmul f (Field.fzero f) C) (Field.fmul f A C)
    s3 = mul-mono (Field.fzero f) A C s1 s2
    -- 0 ≤ A·C   (and 0·C ≡ 0)
    s4 : le (Field.fzero f) (Field.fmul f A C)
    s4 =
      le-rewrite
        (Field.fmul f (Field.fzero f) C)
        (Field.fzero f)
        (Field.fmul f A C)
        (zero-mul F f C)
        s3

------------------------------------------------------------------------
-- The step-up rule.

-- A rank i is "rejected at its own threshold" when its p-value is
-- below thr(i).
bh-rej : (F : Set) → (f : Field F) → (o : Ordered F f) → (m : ℕ) → (q : F) →
  (d : Fin m → F) → (i : Fin m) → Set
bh-rej F f o m q d i =
  Ordered.le o (d i) (bh-threshold F f m q i)

-- Step-up correctness: with the p-values sorted ascending and k the
-- largest rank rejected at its own threshold, the step-up rejection
-- set is exactly the prefix of ranks up to k; every rejected
-- p-value lies below the common cutoff thr(k).

bh-stepup-correct : (F : Set) → (f : Field F) → (o : Ordered F f) →
  (m : ℕ) → (q : F) → (d : Fin m → F) →
  -- p-values sorted ascending:
  (sorted : (i j : Fin m) → fromFin m i ≤N fromFin m j →
            Ordered.le o (d i) (d j)) →
  -- q is non-negative and m is positive in the field:
  (hq : Ordered.le o (Field.fzero f) q) →
  (hNE : natToField F f m ≢ Field.fzero f) →
  (k : Fin m) →
  -- k is rejected at its own threshold:
  bh-rej F f o m q d k →
  -- and no rank above k is rejected at its own threshold:
  ((j : Fin m) → fromFin m k <N fromFin m j →
      ¬ bh-rej F f o m q d j) →
  (i : Fin m) →
  -- (1) every rank in the prefix up to k is rejected by the step-up
  --     (its p-value lies below the common cutoff thr k);
  (fromFin m i ≤N fromFin m k →
     Ordered.le o (d i) (bh-threshold F f m q k)) ×
  -- (2) every rank above k is not rejected at its own threshold
  --     (the maximality premise, restated);
  ((fromFin m k <N fromFin m i →
     ¬ Ordered.le o (d i) (bh-threshold F f m q i)) ×
  -- (3) every rank above k is not below the common cutoff thr k
  --     either — this is where threshold monotonicity is used, and
  --     it is what makes the step-up scan sound.
   (fromFin m k <N fromFin m i →
     ¬ Ordered.le o (d i) (bh-threshold F f m q k)))
bh-stepup-correct F f o m q d sorted hq hNE k hk hn i =
  pair hij-accept (pair hij-reject-own hij-reject-common)
  where
    open Ordered o
      using (le ; le-refl ; le-trans ; le-total ; le-rewrite ;
             le-rewrite-r ; add-mono ; mul-mono ; nat-embed-mono ;
             zero-≤-one ; inv-pos)
    -- a ≤ a+1, hence a < b  ⇒  a ≤ b   (from  a <N b  =  suc a ≤N b)
    ≤N-suc : (a : ℕ) → a ≤N suc a
    ≤N-suc a = (suc zero , sym (m-plus-one a))
    ≤N-from-<N : (a b : ℕ) → a <N b → a ≤N b
    ≤N-from-<N a b e = ≤N-trans (≤N-suc a) e
    hij-accept : fromFin m i ≤N fromFin m k →
      le (d i) (bh-threshold F f m q k)
    hij-accept hij =
      le-trans (d i) (d k) (bh-threshold F f m q k)
               (sorted i k hij) hk
    hij-reject-own : fromFin m k <N fromFin m i →
      ¬ le (d i) (bh-threshold F f m q i)
    hij-reject-own hij′ = hn i hij′
    hij-reject-common : fromFin m k <N fromFin m i →
      ¬ le (d i) (bh-threshold F f m q k)
    hij-reject-common hij′ h =
      hn i hij′
        (le-trans (d i) (bh-threshold F f m q k) (bh-threshold F f m q i)
                 h
                 (bh-threshold-monotone F f o m q k i
                    (≤N-from-<N (fromFin m k) (fromFin m i) hij′)
                    hq
                    hNE))
