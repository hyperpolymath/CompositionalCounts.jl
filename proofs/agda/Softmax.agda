{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- CompositionalCounts.jl — machine-checked algebraic claims.
--
-- Softmax : the softmax over an abstract field with an exponential
-- structure, and its key invariance:
--
--   softmax (v + c)  ≡  softmax v          (common shift c)
--
-- which is the algebraic core of the reference-change / fitted-
-- probability invariance claims for the multinomial and
-- Dirichlet-multinomial models.
--
-- House style (see Basics): every parameter explicit; every implicit
-- parameter used in a clause body named in the clause head; no
-- forward references.
------------------------------------------------------------------------

module Softmax where

open import Basics
open import Nat
open import Vec
open import Field
open import Fin using (Fin ; fromFin ; fsuc) renaming (fzero to finZero)
open import Agda.Builtin.Nat      using (zero ; suc ; _+_ ; _*_)
open import Agda.Builtin.Bool     using (Bool ; true ; false)
open import Agda.Builtin.Equality using (_≡_ ; refl)
open import Agda.Builtin.Sigma    using (Σ ; fst ; snd ; _,_)
open import Agda.Builtin.Unit     using (⊤ ; tt)

------------------------------------------------------------------------
-- The exp-map of a vector.

expmap : (F : Set) → (f : Field F) → (e : Exp F f) → (n : ℕ) →
  Vec F n → Vec F n
expmap F f e n v = vmap F F n (Exp.exp e) v

-- exp is pointwise: vlookup (expmap v) k ≡ exp (vlookup v k)
expmap-lookup : (F : Set) → (f : Field F) → (e : Exp F f) → (n : ℕ) →
  (v : Vec F n) → (k : Fin n) →
  vlookup F n (expmap F f e n v) k ≡ Exp.exp e (vlookup F n v k)
expmap-lookup F f e zero v i with i
expmap-lookup F f e zero v i | (k₀ , e₁) with k₀
expmap-lookup F f e zero v i | (k₀ , e₁) | zero with e₁
expmap-lookup F f e zero v i | (k₀ , e₁) | zero | ()
expmap-lookup F f e zero v i | (k₀ , e₁) | (suc k₁) with e₁
expmap-lookup F f e zero v i | (k₀ , e₁) | (suc k₁) | ()
expmap-lookup F f e (suc n) v k with k
expmap-lookup F f e (suc n) v k | (zero , e₀) = refl
expmap-lookup F f e (suc n) v k | (suc k₁ , e₀) =
  expmap-lookup F f e n (snd v) (k₁ , e₀)

-- Pointwise addition, at the lookup level.
vlookup-vadd : (F : Set) → (f : Field F) → (n : ℕ) → (v w : Vec F n) →
  (k : Fin n) →
  vlookup F n (vadd F f n v w) k ≡
  Field.fplus f (vlookup F n v k) (vlookup F n w k)
vlookup-vadd F f zero v1 v2 i with i
vlookup-vadd F f zero v1 v2 i | (k₀ , e) with k₀
vlookup-vadd F f zero v1 v2 i | (k₀ , e) | zero with e
vlookup-vadd F f zero v1 v2 i | (k₀ , e) | zero | ()
vlookup-vadd F f zero v1 v2 i | (k₀ , e) | (suc k₁) with e
vlookup-vadd F f zero v1 v2 i | (k₀ , e) | (suc k₁) | ()
vlookup-vadd F f (suc n) (a , v1) (b , v2) k with k
vlookup-vadd F f (suc n) (a , v1) (b , v2) k | (zero , e₀) = refl
vlookup-vadd F f (suc n) (a , v1) (b , v2) k | (suc k₁ , e₀) =
  vlookup-vadd F f n v1 v2 (k₁ , e₀)

-- Pointwise scaling, at the lookup level.
vlookup-vscale : (F : Set) → (f : Field F) → (n : ℕ) → (c : F) →
  (v : Vec F n) → (k : Fin n) →
  vlookup F n (vscale F f n c v) k ≡
  Field.fmul f c (vlookup F n v k)
vlookup-vscale F f zero c v i with i
vlookup-vscale F f zero c v i | (k₀ , e) with k₀
vlookup-vscale F f zero c v i | (k₀ , e) | zero with e
vlookup-vscale F f zero c v i | (k₀ , e) | zero | ()
vlookup-vscale F f zero c v i | (k₀ , e) | (suc k₁) with e
vlookup-vscale F f zero c v i | (k₀ , e) | (suc k₁) | ()
vlookup-vscale F f (suc n) c (a , v) k with k
vlookup-vscale F f (suc n) c (a , v) k | (zero , e₀) = refl
vlookup-vscale F f (suc n) c (a , v) k | (suc k₁ , e₀) =
  vlookup-vscale F f n c v (k₁ , e₀)

-- exp (v + c)  =  exp c • exp v   (pointwise scaling of the exp-map)
expmap-vadd : (F : Set) → (f : Field F) → (e : Exp F f) → (n : ℕ) →
  (v : Vec F n) → (c : F) →
  expmap F f e n (vadd F f n v (vreplicate F n c)) ≡
  vscale F f n (Exp.exp e c) (expmap F f e n v)
expmap-vadd F f e n v c =
  vec-ext F n (expmap F f e n (vadd F f n v (vreplicate F n c)))
            (vscale F f n (Exp.exp e c) (expmap F f e n v))
            (λ k →
              trans
                (expmap-lookup F f e n (vadd F f n v (vreplicate F n c)) k)
                (trans
                  (cong (Exp.exp e)
                        (trans (vlookup-vadd F f n v (vreplicate F n c) k)
                               (cong (λ x → Field.fplus f (vlookup F n v k) x)
                                     (vlookup-replicate F n c k))))
                  (trans
                    (Exp.exp-plus e (vlookup F n v k) c)
                    (trans
                      (Field.mul-comm f (Exp.exp e (vlookup F n v k)) (Exp.exp e c))
                      (trans
                        (cong (λ x → Field.fmul f (Exp.exp e c) x)
                              (sym (expmap-lookup F f e n v k)))
                        (sym (vlookup-vscale F f n (Exp.exp e c)
                                           (expmap F f e n v) k)))))))

-- The denominator of the shifted vector.
expmap-sum : (F : Set) → (f : Field F) → (e : Exp F f) → (n : ℕ) →
  (v : Vec F n) → (c : F) →
  vsum F f n (expmap F f e n (vadd F f n v (vreplicate F n c))) ≡
  Field.fmul f (Exp.exp e c)
            (vsum F f n (expmap F f e n v))
expmap-sum F f e n v c =
  trans
    (cong (vsum F f n) (expmap-vadd F f e n v c))
    (vsum-vscale F f n (Exp.exp e c) (expmap F f e n v))

------------------------------------------------------------------------
-- The vector softmax.

-- The j-th softmax component with explicit denominator.
softmax-with : (F : Set) → (f : Field F) → (e : Exp F f) → (n : ℕ) →
  (v : Vec F n) → (S : F) → (s : S ≢ Field.fzero f) → (k : Fin n) → F
softmax-with F f e n v S s k =
  Field.fmul f (Exp.exp e (vlookup F n v k)) (Field.finv f S)

-- The softmax vector.
softmax : (F : Set) → (f : Field F) → (e : Exp F f) → (n : ℕ) →
  (v : Vec F n) →
  (s : vsum F f n (expmap F f e n v) ≢ Field.fzero f) → Vec F n
softmax F f e n v s =
  vecOfLookup F n
    (λ k → softmax-with F f e n v
                (vsum F f n (expmap F f e n v)) s k)

------------------------------------------------------------------------
-- Theorem (softmax shift invariance):
--
--   softmax (v +ᵥ c)  ≡  softmax v
--
-- i.e. adding the same constant to every entry leaves the fitted
-- probabilities unchanged.

-- NB: both denominators are premises; the caller derives the shifted
-- one from the unshifted one with `expmap-sum` + `mul-neq-zero`
-- (the denominator only *propositionally* equals `exp c * S`).
softmax-shift-invariance : (F : Set) → (f : Field F) → (e : Exp F f) →
  (n : ℕ) → (v : Vec F n) → (c : F) →
  (s : vsum F f n (expmap F f e n v) ≢ Field.fzero f) →
  (s′ : vsum F f n (expmap F f e n (vadd F f n v (vreplicate F n c)))
             ≢ Field.fzero f) →
  softmax F f e n
    (vadd F f n v (vreplicate F n c)) s′
    ≡ softmax F f e n v s
softmax-shift-invariance F f e n v c s s′ =
  vec-ext F n (softmax F f e n (vadd F f n v (vreplicate F n c)) s′)
            (softmax F f e n v s)
            (λ k → p k)
  where
    S  : F
    S  = vsum F f n (expmap F f e n v)
    S′ : F
    S′ = vsum F f n (expmap F f e n (vadd F f n v (vreplicate F n c)))
    d1 : S′ ≡ Field.fmul f (Exp.exp e c) S
    d1 = expmap-sum F f e n v c
    p : (k : Fin n) →
        vlookup F n (softmax F f e n (vadd F f n v (vreplicate F n c)) s′) k
        ≡ vlookup F n (softmax F f e n v s) k
    p k =
      trans (vecOfLookup-lookup F n
                 (λ j → softmax-with F f e n
                          (vadd F f n v (vreplicate F n c)) S′ s′ j) k)
            (trans a1 (trans a2 (trans a3 (trans a4 (trans a5
                              (trans a6 (trans a7 (trans a8 (trans a9
                                   (trans a10 a11))))))))))
      where
        eV  : F
        eV  = Exp.exp e (vlookup F n v k)
        eC  : F
        eC  = Exp.exp e c
        ivS : F
        ivS = Field.finv f S
        iec : F
        iec = Field.finv f eC
        a1 : Field.fmul f (Exp.exp e (vlookup F n
                                      (vadd F f n v (vreplicate F n c)) k))
                   (Field.finv f S′)
           ≡ Field.fmul f (Exp.exp e (Field.fplus f (vlookup F n v k)
                                                       (vlookup F n
                                                                (vreplicate F n c) k)))
                   (Field.finv f S′)
        a1 = cong (λ x → Field.fmul f (Exp.exp e x) (Field.finv f S′))
             (vlookup-vadd F f n v (vreplicate F n c) k)
        a2 : Field.fmul f (Exp.exp e (Field.fplus f (vlookup F n v k)
                                                   (vlookup F n
                                                            (vreplicate F n c) k)))
                 (Field.finv f S′)
           ≡ Field.fmul f (Field.fmul f eV eC) (Field.finv f S′)
        a2 = cong (λ x → Field.fmul f x (Field.finv f S′))
             (trans (cong (Exp.exp e)
                          (cong (λ x → Field.fplus f (vlookup F n v k) x)
                                (vlookup-replicate F n c k)))
                    (Exp.exp-plus e (vlookup F n v k) c))
        a3 : Field.fmul f (Field.fmul f eV eC) (Field.finv f S′)
           ≡ Field.fmul f (Field.fmul f eV eC) (Field.finv f (Field.fmul f eC S))
        a3 = cong (λ x → Field.fmul f (Field.fmul f eV eC) x)
             (cong (Field.finv f) d1)
        a4 : Field.fmul f (Field.fmul f eV eC) (Field.finv f (Field.fmul f eC S))
           ≡ Field.fmul f (Field.fmul f eV eC) (Field.fmul f ivS iec)
        a4 = cong (λ x → Field.fmul f (Field.fmul f eV eC) x)
             (inv-mul F f eC S (exp-neq-zero F f e c) s)
        a5 : Field.fmul f (Field.fmul f eV eC) (Field.fmul f ivS iec)
           ≡ Field.fmul f eV (Field.fmul f eC (Field.fmul f ivS iec))
        a5 = Field.mul-assoc f eV eC (Field.fmul f ivS iec)
        a6 : Field.fmul f eV (Field.fmul f eC (Field.fmul f ivS iec))
           ≡ Field.fmul f eV (Field.fmul f (Field.fmul f eC ivS) iec)
        a6 = cong (λ x → Field.fmul f eV x)
             (sym (Field.mul-assoc f eC ivS iec))
        a7 : Field.fmul f eV (Field.fmul f (Field.fmul f eC ivS) iec)
           ≡ Field.fmul f eV (Field.fmul f (Field.fmul f ivS eC) iec)
        a7 = cong (λ x → Field.fmul f eV x)
             (cong (λ y → Field.fmul f y iec)
                   (Field.mul-comm f eC ivS))
        a8 : Field.fmul f eV (Field.fmul f (Field.fmul f ivS eC) iec)
           ≡ Field.fmul f eV (Field.fmul f ivS (Field.fmul f eC iec))
        a8 = cong (λ x → Field.fmul f eV x)
             (Field.mul-assoc f ivS eC iec)
        a9 : Field.fmul f eV (Field.fmul f ivS (Field.fmul f eC iec))
           ≡ Field.fmul f eV (Field.fmul f ivS (Field.fone f))
        a9 = cong (λ x → Field.fmul f eV x)
             (cong (λ y → Field.fmul f ivS y)
                   (Field.inv-ne f eC (exp-neq-zero F f e c)))
        a10 : Field.fmul f eV (Field.fmul f ivS (Field.fone f))
            ≡ Field.fmul f eV ivS
        a10 = cong (λ x → Field.fmul f eV x)
               (Field.mul-one f ivS)
        a11 : Field.fmul f eV ivS
            ≡ vlookup F n (softmax F f e n v s) k
        a11 = sym (vecOfLookup-lookup F n (λ j → softmax-with F f e n v S s j) k)

------------------------------------------------------------------------
-- Sums over finite indices.

fsum : (F : Set) → (f : Field F) → (n : ℕ) → (Fin n → F) → F
fsum F f zero g = Field.fzero f
fsum F f (suc n) g =
  Field.fplus f (g (finZero n))
               (fsum F f n (λ (k , e) → g (fsuc n (k , e))))

-- fsum distributes over pointwise scaling.
fsum-vscale : (F : Set) → (f : Field F) → (n : ℕ) → (c : F) →
  (g : Fin n → F) →
  fsum F f n (λ (k , e) → Field.fmul f (g (k , e)) c) ≡
  Field.fmul f (fsum F f n g) c
fsum-vscale F f zero c g =
  sym (trans (Field.mul-comm f (Field.fzero f) c)
             (Field.mul-zero f c))
fsum-vscale F f (suc n) c g =
  trans
    (cong (λ x → Field.fplus f (Field.fmul f (g (finZero n)) c) x) ih)
    (sym (Field.mul-distr-r F f (g (finZero n)) s c))
  where
    s : F
    s = fsum F f n (λ (k , e) → g (fsuc n (k , e)))
    ih : fsum F f n (λ (k , e) → Field.fmul f (g (fsuc n (k , e))) c)
       ≡ Field.fmul f s c
    ih = fsum-vscale F f n c (λ (k , e) → g (fsuc n (k , e)))

-- The vector sum of vecOfLookup is the finite sum.
vsum-vecOfLookup : (F : Set) → (f : Field F) → (n : ℕ) → (g : Fin n → F) →
  vsum F f n (vecOfLookup F n g) ≡ fsum F f n g
vsum-vecOfLookup F f zero g = refl
vsum-vecOfLookup F f (suc n) g =
  cong (λ x → Field.fplus f (g (finZero n)) x)
       (vsum-vecOfLookup F f n (λ (k , e) → g (fsuc n (k , e))))

-- Theorem: the softmax components sum to one.
softmax-sums-to-one : (F : Set) → (f : Field F) → (e : Exp F f) →
  (n : ℕ) → (v : Vec F n) →
  (s : vsum F f n (expmap F f e n v) ≢ Field.fzero f) →
  vsum F f n (softmax F f e n v s) ≡ Field.fone f
softmax-sums-to-one F f e n v s =
  trans
    (vsum-vecOfLookup F f n (λ (k , e₀) → softmax-with F f e n v S s (k , e₀)))
    (trans
      (fsum-vscale F f n (Field.finv f S)
                   (λ (k , e₀) → Exp.exp e (vlookup F n v (k , e₀))))
      (trans
        (cong (λ x → Field.fmul f x (Field.finv f S)) bridge)
        (Field.inv-ne f S s)))
  where
    S : F
    S = vsum F f n (expmap F f e n v)
    -- fsum (λ k → exp (vlookup v k))  ≡  vsum (expmap v)
    bridge : fsum F f n (λ (k , e₀) → Exp.exp e (vlookup F n v (k , e₀)))
           ≡ S
    bridge =
      trans
        (sym (vsum-vecOfLookup F f n (λ (k , e₀) → Exp.exp e (vlookup F n v (k , e₀)))))
        (cong (vsum F f n)
              (vec-ext F n
                 (vecOfLookup F n (λ (k , e₀) → Exp.exp e (vlookup F n v (k , e₀))))
                 (expmap F f e n v)
                 (λ (k , e₀) →
                   trans
                     (vecOfLookup-lookup F n (λ (j , e₁) → Exp.exp e (vlookup F n v (j , e₁))) (k , e₀))
                     (sym (expmap-lookup F f e n v (k , e₀))))))
