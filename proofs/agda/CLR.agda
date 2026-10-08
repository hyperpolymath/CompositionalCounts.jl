{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- CompositionalCounts.jl — machine-checked algebraic claims.
--
-- CLR : the centered log-ratio transform of a logit/effect vector.
--
--     clr β_j = β_j − (1/J) · Σ_k β_k
--
-- and the claims:
--
--   * the CLR effects sum to zero (the effects span the zero-sum
--     subspace);
--   * re-centering is idempotent: applying CLR twice is the same as
--     applying it once.
--
-- Both need the premise that the embedded natural number J is nonzero
-- in the field (for the reals: J ≥ 1, as required by the method).
--
-- House style (see Basics): every parameter explicit; every implicit
-- parameter used in a clause body named in the clause head; no
-- forward references.
------------------------------------------------------------------------

module CLR where

open import Basics
open import Nat
open import Vec
open import Field
open import Agda.Builtin.Nat      using (zero ; suc ; _+_ ; _*_)
open import Agda.Builtin.Bool     using (Bool ; true ; false)
open import Agda.Builtin.Equality using (_≡_ ; refl)
open import Agda.Builtin.Sigma    using (Σ ; fst ; snd ; _,_)
open import Agda.Builtin.Unit     using (⊤ ; tt)

------------------------------------------------------------------------
-- The transform.

-- The center of β:  (1/J) · Σ β.
center : (F : Set) → (f : Field F) → (J : ℕ) → (β : Vec F J) → F
center F f J β =
  Field.fmul f (Field.finv f (natToField F f J)) (vsum F f J β)

-- clr β_j = β_j − center β.
clr : (F : Set) → (f : Field F) → (J : ℕ) → (β : Vec F J) → Vec F J
clr F f J β =
  vmap F F J (λ x → fminus F f x (center F f J β)) β

------------------------------------------------------------------------
-- Claim: the CLR effects sum to zero.

clr-sum-zero : (F : Set) → (f : Field F) → (J : ℕ) → (β : Vec F J) →
  natToField F f J ≢ Field.fzero f →
  vsum F f J (clr F f J β) ≡ Field.fzero f
clr-sum-zero F f J β hJ =
  trans t1 (trans t2 (trans t3 (trans t4 (trans t5 t6))))
  where
    c : F
    c = center F f J β
    s : F
    s = vsum F f J β
    NTJ : F
    NTJ = natToField F f J
    -- vmap (λ x → x − c) β  ≡  β +ᵥ (−c)
    vmap-fminus : (F : Set) → (f : Field F) → (J : ℕ) → (β : Vec F J) →
      (c : F) →
      vmap F F J (λ x → fminus F f x c) β ≡
      vadd F f J β (vreplicate F J (Field.fneg f c))
    vmap-fminus F f zero β c = refl
    vmap-fminus F f (suc J) (a , β) c =
      cong (λ t → Field.fplus f a (Field.fneg f c) , t)
           (vmap-fminus F f J β c)
    t1 : vsum F f J (clr F f J β)
       ≡ vsum F f J (vadd F f J β (vreplicate F J (Field.fneg f c)))
    t1 = cong (λ x → vsum F f J x) (vmap-fminus F f J β c)
    t2 : vsum F f J (vadd F f J β (vreplicate F J (Field.fneg f c)))
       ≡ Field.fplus f s (vsum F f J (vreplicate F J (Field.fneg f c)))
    t2 = vsum-vadd F f J β (vreplicate F J (Field.fneg f c))
    t3 : Field.fplus f s (vsum F f J (vreplicate F J (Field.fneg f c)))
       ≡ Field.fplus f s (Field.fmul f NTJ (Field.fneg f c))
    t3 = cong (λ x → Field.fplus f s x) (vsum-const F f J (Field.fneg f c))
    t4 : Field.fplus f s (Field.fmul f NTJ (Field.fneg f c))
       ≡ Field.fplus f s (Field.fneg f (Field.fmul f NTJ c))
    t4 =
      trans
        (trans
          (cong (λ x → Field.fplus f s x)
                (Field.mul-comm f NTJ (Field.fneg f c)))
          (cong (λ x → Field.fplus f s x)
                (sym (neg-mul F f c NTJ))))
        (cong (λ x → Field.fplus f s (Field.fneg f x))
              (Field.mul-comm f c NTJ))
    t5 : Field.fplus f s (Field.fneg f (Field.fmul f NTJ c))
       ≡ Field.fplus f s
                      (Field.fneg f
                         (Field.fmul f (Field.fmul f NTJ (Field.finv f NTJ)) s))
    t5 = cong (λ x → Field.fplus f s (Field.fneg f x))
         (sym (Field.mul-assoc f NTJ (Field.finv f NTJ) s))
    t6 : Field.fplus f s
           (Field.fneg f
              (Field.fmul f (Field.fmul f NTJ (Field.finv f NTJ)) s))
       ≡ Field.fzero f
    t6 =
      trans
        (cong (λ x → Field.fplus f s (Field.fneg f x))
              (cong (λ y → Field.fmul f y s)
                    (Field.inv-ne f NTJ hJ)))
        (trans
          (cong (λ x → Field.fplus f s (Field.fneg f x))
                (Field.one-mul f s))
          (Field.plus-neg f s))

------------------------------------------------------------------------
-- Claim: re-centering is idempotent.

clr-stable : (F : Set) → (f : Field F) → (J : ℕ) → (β : Vec F J) →
  natToField F f J ≢ Field.fzero f →
  clr F f J (clr F f J β) ≡ clr F f J β
clr-stable F f J β hJ =
  vec-ext F J (clr F f J (clr F f J β)) (clr F f J β)
           (λ k →
             trans
               (vlookup-vmap F F J (λ x → fminus F f x (center F f J (clr F f J β)))
                             (clr F f J β) k)
               (trans
                 (cong (λ x → fminus F f (vlookup F J (clr F f J β) k) x)
                       (cong (λ y → Field.fmul f (Field.finv f (natToField F f J)) y)
                             (clr-sum-zero F f J β hJ)))
                 (trans
                   (cong (λ x → fminus F f (vlookup F J (clr F f J β) k) x)
                         (Field.mul-zero f (Field.finv f (natToField F f J))))
                   (fminus-0 F f (vlookup F J (clr F f J β) k)))))
