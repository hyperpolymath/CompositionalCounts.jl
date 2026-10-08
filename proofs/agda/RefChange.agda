{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- CompositionalCounts.jl — machine-checked algebraic claims.
--
-- RefChange : reference-taxon change for multinomial logits.
--
-- Re-anchoring a logit vector β at reference r produces
--
--     η_j = β_j − β_r
--
-- and we prove:
--
--   * the new logit at the reference is exactly zero;
--   * the operation is a bijection on the logit subspace: the pair
--     (η, β_r) remembers everything (round-trip), and re-anchoring is
--     invariant under adding a common shift to all entries;
--   * the fitted probabilities are unchanged (MN-1 core):
--         softmax (refchg β r)  ≡  softmax β.
--
-- House style (see Basics): every parameter explicit; every implicit
-- parameter used in a clause body named in the clause head; no
-- forward references.
------------------------------------------------------------------------

module RefChange where

open import Basics
open import Nat
open import Vec
open import Field
open import Softmax
open import Fin using (Fin ; fromFin ; fsuc) renaming (fzero to finZero)
open import Agda.Builtin.Nat      using (zero ; suc ; _+_ ; _*_)
open import Agda.Builtin.Bool     using (Bool ; true ; false)
open import Agda.Builtin.Equality using (_≡_ ; refl)
open import Agda.Builtin.Sigma    using (Σ ; fst ; snd ; _,_)
open import Agda.Builtin.Unit     using (⊤ ; tt)

------------------------------------------------------------------------
-- The operation.

-- Re-anchor β at reference r:  η_j = β_j − β_r.
refchg : (F : Set) → (f : Field F) → (J : ℕ) → (β : Vec F J) →
  (r : Fin J) → Vec F J
refchg F f J β r =
  vmap F F J (λ x → fminus F f x (vlookup F J β r)) β

-- The inverse move: add a common offset β_r to every entry.
unrefchg : (F : Set) → (f : Field F) → (J : ℕ) → (η : Vec F J) →
  (βr : F) → (r : Fin J) → Vec F J
unrefchg F f J η βr r =
  vmap F F J (λ x → Field.fplus f x βr) η

------------------------------------------------------------------------
-- (a − b) + b ≡ a
fminus-then-add : (F : Set) → (f : Field F) → (a b : F) →
  Field.fplus f (fminus F f a b) b ≡ a
fminus-then-add F f a b =
  trans
    (Field.plus-assoc f a (Field.fneg f b) b)
    (trans
      (cong (λ x → Field.fplus f a x) (Field.plus-comm f (Field.fneg f b) b))
      (trans
        (cong (λ x → Field.fplus f a x) (Field.plus-neg f b))
        (Field.plus-zero f a)))

------------------------------------------------------------------------
-- The re-anchored logit at the reference is zero.

refchg-zero : (F : Set) → (f : Field F) → (J : ℕ) → (β : Vec F J) →
  (r : Fin J) → vlookup F J (refchg F f J β r) r ≡ Field.fzero f
refchg-zero F f J β r =
  trans
    (vlookup-vmap F F J (λ x → fminus F f x (vlookup F J β r)) β r)
    (fminus-self F f (vlookup F J β r))

-- Re-anchoring is a common shift:  refchg β r  =  β +ᵥ (−β_r).

refchg-is-shift : (F : Set) → (f : Field F) → (J : ℕ) → (β : Vec F J) →
  (r : Fin J) →
  refchg F f J β r ≡
  vadd F f J β (vreplicate F J (Field.fneg f (vlookup F J β r)))
refchg-is-shift F f J β r =
  vec-ext F J (refchg F f J β r)
            (vadd F f J β (vreplicate F J (Field.fneg f (vlookup F J β r))))
            (λ k →
              trans
                (vlookup-vmap F F J (λ x → fminus F f x (vlookup F J β r)) β k)
                (sym (trans
                       (vlookup-vadd F f J β
                         (vreplicate F J (Field.fneg f (vlookup F J β r))) k)
                       (cong (λ x → Field.fplus f (vlookup F J β k) x)
                             (vlookup-replicate F J
                               (Field.fneg f (vlookup F J β r)) k)))))

-- Round-trip:  unrefchg (refchg β r) (β_r) r  =  β.

refchg-roundtrip : (F : Set) → (f : Field F) → (J : ℕ) → (β : Vec F J) →
  (r : Fin J) →
  unrefchg F f J (refchg F f J β r) (vlookup F J β r) r ≡ β
refchg-roundtrip F f J β r =
  vec-ext F J (unrefchg F f J (refchg F f J β r) (vlookup F J β r) r) β
            (λ k →
              trans
                (vlookup-vmap F F J (λ x → Field.fplus f x (vlookup F J β r))
                              (refchg F f J β r) k)
                (trans
                  (cong (λ x → Field.fplus f x (vlookup F J β r))
                        (vlookup-vmap F F J
                           (λ x → fminus F f x (vlookup F J β r)) β k))
                  (fminus-then-add F f (vlookup F J β k)
                                   (vlookup F J β r))))

-- Re-anchoring forgets common shifts:
--   refchg (β +ᵥ b) r  =  refchg β r.

refchg-shift-invariant : (F : Set) → (f : Field F) → (J : ℕ) →
  (β : Vec F J) → (r : Fin J) → (b : F) →
  refchg F f J (vadd F f J β (vreplicate F J b)) r ≡
  refchg F f J β r
refchg-shift-invariant F f J β r b =
  vec-ext F J (refchg F f J (vadd F f J β (vreplicate F J b)) r)
            (refchg F f J β r)
            (λ k →
              trans
                (vlookup-vmap F F J
                   (λ x → fminus F f x
                          (vlookup F J (vadd F f J β (vreplicate F J b)) r))
                   (vadd F f J β (vreplicate F J b)) k)
                (trans
                  (cong
                    (λ y → fminus F f y
                            (vlookup F J (vadd F f J β (vreplicate F J b)) r))
                    (trans
                      (vlookup-vadd F f J β (vreplicate F J b) k)
                      (cong (λ x → Field.fplus f (vlookup F J β k) x)
                            (vlookup-replicate F J b k))))
                  (trans
                    (cong
                      (λ x → fminus F f (Field.fplus f (vlookup F J β k) b) x)
                      (trans
                        (vlookup-vadd F f J β (vreplicate F J b) r)
                        (cong (λ x → Field.fplus f (vlookup F J β r) x)
                              (vlookup-replicate F J b r))))
                    (trans
                      (cong
                        (λ y → fminus F f y
                                (Field.fplus f (vlookup F J β r) b))
                        (cong (λ x → Field.fplus f (vlookup F J β k) x)
                              (Field.neg-neg F f b)))
                      (trans
                        (cong
                          (λ x → fminus F f (fminus F f (vlookup F J β k)
                                                          (Field.fneg f b)) x)
                          (cong (λ x → Field.fplus f (vlookup F J β r) x)
                                (Field.neg-neg F f b)))
                        (trans
                          (fminus-fminus F f (vlookup F J β k)
                                         (vlookup F J β r) (Field.fneg f b))
                          (sym (vlookup-vmap F F J
                                   (λ x → fminus F f x (vlookup F J β r))
                                   β k))))))))

------------------------------------------------------------------------
-- MN-1 core: fitted probabilities are invariant under reference
-- change (both denominances nonzero).

refchg-prob-invariance : (F : Set) → (f : Field F) → (e : Exp F f) →
  (J : ℕ) → (β : Vec F J) → (r : Fin J) →
  (s : vsum F f J (expmap F f e J β) ≢ Field.fzero f) →
  (s′ : vsum F f J (expmap F f e J (refchg F f J β r)) ≢ Field.fzero f) →
  softmax F f e J (refchg F f J β r) s′ ≡ softmax F f e J β s
refchg-prob-invariance F f e J β r s s′ =
  vec-ext F J (softmax F f e J (refchg F f J β r) s′)
            (softmax F f e J β s)
            (λ k → p k)
  where
    S  : F
    S  = vsum F f J (expmap F f e J β)
    S′ : F
    S′ = vsum F f J (expmap F f e J (refchg F f J β r))
    -- S′  ≡  exp (−β_r) * S
    S′-eq : S′ ≡ Field.fmul f (Exp.exp e (Field.fneg f (vlookup F J β r))) S
    S′-eq =
      trans
        (cong (λ w → vsum F f J (expmap F f e J w))
              (refchg-is-shift F f J β r))
        (trans
          (cong (vsum F f J)
                (expmap-vadd F f e J β (Field.fneg f (vlookup F J β r))))
          (vsum-vscale F f J (Exp.exp e (Field.fneg f (vlookup F J β r)))
                       (expmap F f e J β)))
    p : (k : Fin J) →
        vlookup F J (softmax F f e J (refchg F f J β r) s′) k
        ≡ vlookup F J (softmax F f e J β s) k
    p k =
      trans a0 (trans a1 (trans a2 (trans a3 (trans a5 a11))))
      where
        eV  : F
        eV  = Exp.exp e (vlookup F J β k)
        eC  : F
        eC  = Exp.exp e (Field.fneg f (vlookup F J β r))
        a0 : vlookup F J (softmax F f e J (refchg F f J β r) s′) k
           ≡ Field.fmul f (Exp.exp e (vlookup F J (refchg F f J β r) k))
                           (Field.finv f S′)
        a0 = vecOfLookup-lookup F J
                 (λ j → softmax-with F f e J (refchg F f J β r) S′ s′ j) k
        a1 : Field.fmul f (Exp.exp e (vlookup F J (refchg F f J β r) k))
                   (Field.finv f S′)
           ≡ Field.fmul f (Exp.exp e
                   (Field.fplus f (vlookup F J β k)
                                  (Field.fneg f (vlookup F J β r))))
                   (Field.finv f S′)
        a1 = cong (λ x → Field.fmul f (Exp.exp e x) (Field.finv f S′))
             (vlookup-vmap F F J (λ x → fminus F f x (vlookup F J β r)) β k)
        a2 : Field.fmul f (Exp.exp e
                   (Field.fplus f (vlookup F J β k)
                                  (Field.fneg f (vlookup F J β r))))
                   (Field.finv f S′)
           ≡ Field.fmul f (Field.fmul f eV eC) (Field.finv f S′)
        a2 = cong (λ x → Field.fmul f x (Field.finv f S′))
             (Exp.exp-plus e (vlookup F J β k)
                           (Field.fneg f (vlookup F J β r)))
        a3 : Field.fmul f (Field.fmul f eV eC) (Field.finv f S′)
           ≡ Field.fmul f (Field.fmul f eV eC)
                          (Field.finv f (Field.fmul f eC S))
        a3 = cong (λ x → Field.fmul f (Field.fmul f eV eC) x)
             (cong (Field.finv f) S′-eq)
        a5 : Field.fmul f (Field.fmul f eV eC)
                          (Field.finv f (Field.fmul f eC S))
           ≡ Field.fmul f eV (Field.finv f S)
        a5 = mul-canc-factor F f eV eC S
             (exp-neq-zero F f e (Field.fneg f (vlookup F J β r))) s
        a11 : Field.fmul f eV (Field.finv f S)
            ≡ vlookup F J (softmax F f e J β s) k
        a11 = sym (vecOfLookup-lookup F J
                  (λ j → softmax-with F f e J β S s j) k)
