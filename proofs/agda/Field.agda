{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- CompositionalCounts.jl — machine-checked algebraic claims.
--
-- Field : an abstract commutative field (with an optional
-- exponential structure) plus the vector/sum machinery over it.
--
-- Everything is proven for an arbitrary field instance; nothing is
-- postulated beyond the field axioms themselves (which describe the
-- structure, not extra assumptions about a particular field).
--
-- House style (see Basics): every parameter explicit; every implicit
-- parameter used in a clause body named in the clause head; no
-- forward references.
--
-- The record and this module share the name Field, so projections
-- are always used qualified (Field.fplus etc.); record parameters
-- are implicit in projections, so Field.fplus f a b.
------------------------------------------------------------------------

module Field where

open import Basics
open import Nat
open import Vec
open import Fin using (Fin ; fromFin ; fsuc) renaming (fzero to finZero)
open import Agda.Builtin.Nat      using (zero ; suc ; _+_ ; _*_)
open import Agda.Builtin.Bool     using (Bool ; true ; false)
open import Agda.Builtin.Equality using (_≡_ ; refl)
open import Agda.Builtin.Sigma    using (Σ ; fst ; snd ; _,_)
open import Agda.Builtin.Unit     using (⊤ ; tt)

------------------------------------------------------------------------
-- A commutative field, with operations named explicitly (this build
-- cannot use the record's own infix fields inside field types).

record Field (F : Set) : Set where
  field
    fzero  : F
    fone   : F
    fplus  : F → F → F
    fmul   : F → F → F
    fneg   : F → F
    finv   : F → F
    fzero≢fone : ¬ (fzero ≡ fone)
    plus-comm  : (a b : F) → fplus a b ≡ fplus b a
    plus-assoc : (a b c : F) → fplus (fplus a b) c ≡ fplus a (fplus b c)
    zero-plus  : (a : F) → fplus fzero a ≡ a
    plus-zero  : (a : F) → fplus a fzero ≡ a
    plus-neg   : (a : F) → fplus a (fneg a) ≡ fzero
    mul-comm   : (a b : F) → fmul a b ≡ fmul b a
    mul-assoc  : (a b c : F) → fmul (fmul a b) c ≡ fmul a (fmul b c)
    mul-zero   : (a : F) → fmul a fzero ≡ fzero
    mul-one    : (a : F) → fmul a fone ≡ a
    one-mul    : (a : F) → fmul fone a ≡ a
    mul-distr  : (a b c : F) → fmul a (fplus b c) ≡ fplus (fmul a b) (fmul a c)
    inv-ne     : (a : F) → a ≢ fzero → fmul a (finv a) ≡ fone

------------------------------------------------------------------------
-- Subtraction.

-- a - b
fminus : (F : Set) → (f : Field F) → F → F → F
fminus F f a b = Field.fplus f a (Field.fneg f b)

------------------------------------------------------------------------
-- Additive group facts.

-- neg 0 ≡ 0
neg-zero : (F : Set) → (f : Field F) →
  Field.fneg f (Field.fzero f) ≡ Field.fzero f
neg-zero F f =
  trans (sym (Field.zero-plus f (Field.fneg f (Field.fzero f))))
        (Field.plus-neg f (Field.fzero f))

-- 0 · a ≡ 0   (the left zero law, from commutativity and a · 0 ≡ 0)
zero-mul : (F : Set) → (f : Field F) → (a : F) →
  Field.fmul f (Field.fzero f) a ≡ Field.fzero f
zero-mul F f a =
  trans (Field.mul-comm f (Field.fzero f) a)
        (Field.mul-zero f a)

-- a - 0 ≡ a
fminus-0 : (F : Set) → (f : Field F) → (a : F) →
  fminus F f a (Field.fzero f) ≡ a
fminus-0 F f a =
  trans
    (cong (λ x → Field.fplus f a x) (neg-zero F f))
    (Field.plus-zero f a)

-- a - a ≡ 0
fminus-self : (F : Set) → (f : Field F) → (a : F) →
  fminus F f a a ≡ Field.fzero f
fminus-self F f a = Field.plus-neg f a

-- If x + s = 0 then x is the additive inverse of s.
add-inv-unique : (F : Set) → (f : Field F) → (s x : F) →
  Field.fplus f x s ≡ Field.fzero f → x ≡ Field.fneg f s
add-inv-unique F f s x e =
  trans
    (sym (Field.plus-zero f x))
    (trans
      (cong (λ y → Field.fplus f x y) (sym (Field.plus-neg f s)))
      (trans
        (sym (Field.plus-assoc f x s (Field.fneg f s)))
        (trans
          (cong (λ y → Field.fplus f y (Field.fneg f s)) e)
          (Field.zero-plus f (Field.fneg f s)))))

-- neg (neg a) ≡ a
neg-neg : (F : Set) → (f : Field F) → (a : F) →
  a ≡ Field.fneg f (Field.fneg f a)
neg-neg F f a =
  add-inv-unique F f (Field.fneg f a) a (Field.plus-neg f a)

-- neg (a + b) ≡ neg a + neg b
neg-add : (F : Set) → (f : Field F) → (a b : F) →
  Field.fneg f (Field.fplus f a b) ≡
  Field.fplus f (Field.fneg f a) (Field.fneg f b)
neg-add F f a b =
  sym (add-inv-unique F f (Field.fplus f a b)
                      (Field.fplus f (Field.fneg f a) (Field.fneg f b)) n)
  where
    -- (neg a + neg b) + (a + b) ≡ 0
    n : Field.fplus f (Field.fplus f (Field.fneg f a) (Field.fneg f b))
                (Field.fplus f a b) ≡ Field.fzero f
    n =
      trans
        (Field.plus-assoc f (Field.fneg f a) (Field.fneg f b) (Field.fplus f a b))
        (trans
          (cong (λ x → Field.fplus f (Field.fneg f a) x)
                (sym (Field.plus-assoc f (Field.fneg f b) a b)))
          (trans
            (cong (λ x → Field.fplus f (Field.fneg f a) x)
                  (cong (λ y → Field.fplus f y b)
                        (Field.plus-comm f (Field.fneg f b) a)))
            (trans
              (sym (Field.plus-assoc f (Field.fneg f a) (Field.fplus f a (Field.fneg f b)) b))
              (trans
                (cong (λ x → Field.fplus f x b)
                      (sym (Field.plus-assoc f (Field.fneg f a) a (Field.fneg f b))))
                (trans
                  (cong (λ x → Field.fplus f x b)
                        (cong (λ y → Field.fplus f y (Field.fneg f b))
                              (Field.plus-comm f (Field.fneg f a) a)))
                  (trans
                    (cong (λ x → Field.fplus f x b)
                          (cong (λ y → Field.fplus f y (Field.fneg f b))
                                (Field.plus-neg f a)))
                    (trans
                      (cong (λ x → Field.fplus f x b)
                            (Field.zero-plus f (Field.fneg f b)))
                      (trans
                        (Field.plus-comm f (Field.fneg f b) b)
                        (Field.plus-neg f b)))))))))

-- (a - c) - (b - c) ≡ a - b
fminus-fminus : (F : Set) → (f : Field F) → (a b c : F) →
  fminus F f (fminus F f a c) (fminus F f b c) ≡ fminus F f a b
fminus-fminus F f a b c =
  trans t1 (trans t2 (trans t3 (trans t4 (trans t5 (trans t6 (trans t7 (trans t8 t9)))))))
  where
    ac : F
    ac = Field.fplus f a (Field.fneg f c)
    -- (a - c) + neg (b - c)
    t1 : Field.fplus f ac (Field.fneg f (fminus F f b c)) ≡
         Field.fplus f ac (Field.fplus f (Field.fneg f b) (Field.fneg f (Field.fneg f c)))
    t1 =
      cong (λ x → Field.fplus f ac x) (neg-add F f b (Field.fneg f c))
    t2 : Field.fplus f ac (Field.fplus f (Field.fneg f b) (Field.fneg f (Field.fneg f c))) ≡
         Field.fplus f ac (Field.fplus f (Field.fneg f b) c)
    t2 =
      cong (λ x → Field.fplus f ac x)
           (cong (λ y → Field.fplus f (Field.fneg f b) y)
                 (sym (neg-neg F f c)))
    t3 : Field.fplus f ac (Field.fplus f (Field.fneg f b) c) ≡
         Field.fplus f (Field.fplus f ac (Field.fneg f b)) c
    t3 =
      sym (Field.plus-assoc f ac (Field.fneg f b) c)
    t4 : Field.fplus f (Field.fplus f ac (Field.fneg f b)) c ≡
         Field.fplus f (Field.fplus f a (Field.fplus f (Field.fneg f c) (Field.fneg f b))) c
    t4 =
      cong (λ x → Field.fplus f x c)
           (Field.plus-assoc f a (Field.fneg f c) (Field.fneg f b))
    t5 : Field.fplus f (Field.fplus f a (Field.fplus f (Field.fneg f c) (Field.fneg f b))) c ≡
         Field.fplus f (Field.fplus f a (Field.fplus f (Field.fneg f b) (Field.fneg f c))) c
    t5 =
      cong (λ x → Field.fplus f x c)
           (cong (λ y → Field.fplus f a y)
                 (Field.plus-comm f (Field.fneg f c) (Field.fneg f b)))
    t6 : Field.fplus f (Field.fplus f a (Field.fplus f (Field.fneg f b) (Field.fneg f c))) c ≡
         Field.fplus f (Field.fplus f (Field.fplus f a (Field.fneg f b)) (Field.fneg f c)) c
    t6 =
      cong (λ x → Field.fplus f x c)
           (sym (Field.plus-assoc f a (Field.fneg f b) (Field.fneg f c)))
    t7 : Field.fplus f (Field.fplus f (Field.fplus f a (Field.fneg f b)) (Field.fneg f c)) c ≡
         Field.fplus f (Field.fplus f a (Field.fneg f b))
                        (Field.fplus f (Field.fneg f c) c)
    t7 =
      Field.plus-assoc f (Field.fplus f a (Field.fneg f b)) (Field.fneg f c) c
    t8 : Field.fplus f (Field.fplus f a (Field.fneg f b))
                        (Field.fplus f (Field.fneg f c) c) ≡
         Field.fplus f (Field.fplus f a (Field.fneg f b)) (Field.fzero f)
    t8 =
      cong (λ x → Field.fplus f (Field.fplus f a (Field.fneg f b)) x)
           (trans (Field.plus-comm f (Field.fneg f c) c)
                  (Field.plus-neg f c))
    t9 : Field.fplus f (Field.fplus f a (Field.fneg f b)) (Field.fzero f) ≡
         Field.fplus f a (Field.fneg f b)
    t9 =
      Field.plus-zero f (Field.fplus f a (Field.fneg f b))

------------------------------------------------------------------------
-- Multiplicative facts.

-- a * b ≠ 0  →  a ≠ 0
prod-neq-zero-l : (F : Set) → (f : Field F) → (a b : F) →
  Field.fmul f a b ≢ Field.fzero f → a ≢ Field.fzero f
prod-neq-zero-l F f a b ¬h e =
  contradiction
    (trans (cong (λ x → Field.fmul f x b) e)
           (trans (Field.mul-comm f (Field.fzero f) b)
                  (Field.mul-zero f b)))
    ¬h

-- a ≠ 0  and  b ≠ 0  →  a * b ≠ 0
mul-neq-zero : (F : Set) → (f : Field F) → (a b : F) →
  a ≢ Field.fzero f → b ≢ Field.fzero f →
  Field.fmul f a b ≢ Field.fzero f
mul-neq-zero F f a b aNE bNE h =
  contradiction
    (trans
      (sym (Field.one-mul f b))
      (trans
        (cong (λ x → Field.fmul f x b)
              (trans (sym (Field.inv-ne f a aNE))
                     (Field.mul-comm f a (Field.finv f a))))
        (trans
          (Field.mul-assoc f (Field.finv f a) a b)
          (trans
            (cong (λ x → Field.fmul f (Field.finv f a) x) h)
            (Field.mul-zero f (Field.finv f a))))))
    bNE

-- a ≠ 0  →  a * b ≡ a * c  →  b ≡ c
mul-canc : (F : Set) → (f : Field F) → (a b c : F) →
  a ≢ Field.fzero f → Field.fmul f a b ≡ Field.fmul f a c → b ≡ c
mul-canc F f a b c aNE e =
  trans
    (sym (Field.one-mul f b))
    (trans
      (cong (λ x → Field.fmul f x b)
            (trans (sym (Field.inv-ne f a aNE))
                   (Field.mul-comm f a (Field.finv f a))))
      (trans
        (Field.mul-assoc f (Field.finv f a) a b)
        (trans
          (cong (λ x → Field.fmul f (Field.finv f a) x) e)
          (trans
            (sym (Field.mul-assoc f (Field.finv f a) a c))
            (trans
              (cong (λ x → Field.fmul f x c)
                    (trans (Field.mul-comm f (Field.finv f a) a)
                           (Field.inv-ne f a aNE)))
              (Field.one-mul f c))))))

-- Two right inverses of a nonzero element are equal.
inv-unique : (F : Set) → (f : Field F) → (a b c : F) →
  Field.fmul f a b ≡ Field.fone f →
  Field.fmul f a c ≡ Field.fone f → b ≡ c
inv-unique F f a b c e2 e3 =
  trans
    (sym (Field.mul-one f b))
    (trans
      (cong (λ x → Field.fmul f b x) (sym e3))
      (trans
        (sym (Field.mul-assoc f b a c))
        (trans
          (cong (λ x → Field.fmul f x c) (Field.mul-comm f b a))
          (trans
            (cong (λ x → Field.fmul f x c) e2)
            (Field.one-mul f c)))))

-- Right distributivity: (a + b) * c ≡ a * c + b * c
mul-distr-r : (F : Set) → (f : Field F) → (a b c : F) →
  Field.fmul f (Field.fplus f a b) c ≡
  Field.fplus f (Field.fmul f a c) (Field.fmul f b c)
mul-distr-r F f a b c =
  trans
    (Field.mul-comm f (Field.fplus f a b) c)
    (trans
      (Field.mul-distr f c a b)
      (trans
        (cong (λ x → Field.fplus f x (Field.fmul f c b))
              (Field.mul-comm f c a))
        (cong (λ x → Field.fplus f (Field.fmul f a c) x)
              (Field.mul-comm f c b))))

-- neg (a * b) ≡ neg a * b
neg-mul : (F : Set) → (f : Field F) → (a b : F) →
  Field.fneg f (Field.fmul f a b) ≡
  Field.fmul f (Field.fneg f a) b
neg-mul F f a b =
  sym (add-inv-unique F f (Field.fmul f a b)
                      (Field.fmul f (Field.fneg f a) b) x2)
  where
    x2 : Field.fplus f (Field.fmul f (Field.fneg f a) b) (Field.fmul f a b) ≡
         Field.fzero f
    x2 =
      trans
        (sym (mul-distr-r F f (Field.fneg f a) a b))
        (trans
          (cong (λ x → Field.fmul f x b)
                (trans (Field.plus-comm f (Field.fneg f a) a)
                       (Field.plus-neg f a)))
          (trans (Field.mul-comm f (Field.fzero f) b)
                 (Field.mul-zero f b)))

-- inv (a * b) ≡ inv b * inv a
inv-mul : (F : Set) → (f : Field F) → (a b : F) →
  a ≢ Field.fzero f → b ≢ Field.fzero f →
  Field.finv f (Field.fmul f a b) ≡
  Field.fmul f (Field.finv f b) (Field.finv f a)
inv-mul F f a b aNE bNE =
  sym (inv-unique F f (Field.fmul f a b)
             (Field.fmul f (Field.finv f b) (Field.finv f a))
             (Field.finv f (Field.fmul f a b))
             e2
             (Field.inv-ne f (Field.fmul f a b)
                            (mul-neq-zero F f a b aNE bNE)))
  where
    e2 : Field.fmul f (Field.fmul f a b)
              (Field.fmul f (Field.finv f b) (Field.finv f a)) ≡ Field.fone f
    e2 =
      trans
        (Field.mul-assoc f a b (Field.fmul f (Field.finv f b) (Field.finv f a)))
        (trans
          (cong (λ x → Field.fmul f a x)
                (sym (Field.mul-assoc f b (Field.finv f b) (Field.finv f a))))
          (trans
            (cong (λ x → Field.fmul f a x)
                  (cong (λ y → Field.fmul f y (Field.finv f a))
                        (Field.inv-ne f b bNE)))
            (trans
              (cong (λ x → Field.fmul f a x)
                    (Field.one-mul f (Field.finv f a)))
              (Field.inv-ne f a aNE))))

-- x * c * inv (c * S)  ≡  x * inv S     (c ≠ 0, S ≠ 0)
-- The common factor c cancels across the multiplicative inverse.
mul-canc-factor : (F : Set) → (f : Field F) → (x c S : F) →
  c ≢ Field.fzero f → S ≢ Field.fzero f →
  Field.fmul f (Field.fmul f x c) (Field.finv f (Field.fmul f c S)) ≡
  Field.fmul f x (Field.finv f S)
mul-canc-factor F f x c S cNE SNE =
  trans
    (Field.mul-assoc f x c (Field.finv f (Field.fmul f c S)))
    (trans
      (cong (λ y → Field.fmul f x y)
            (cong (λ z → Field.fmul f c z)
                  (inv-mul F f c S cNE SNE)))
      (trans
        (cong (λ y → Field.fmul f x y)
              (sym (Field.mul-assoc f c (Field.finv f S) (Field.finv f c))))
        (trans
          (cong (λ y → Field.fmul f x y)
                (cong (λ z → Field.fmul f z (Field.finv f c))
                      (Field.mul-comm f c (Field.finv f S))))
          (trans
            (cong (λ y → Field.fmul f x y)
                  (Field.mul-assoc f (Field.finv f S) c
                                    (Field.finv f c)))
            (trans
              (cong (λ y → Field.fmul f x y)
                    (cong (λ z → Field.fmul f (Field.finv f S) z)
                          (Field.inv-ne f c cNE)))
              (cong (λ y → Field.fmul f x y)
                    (Field.mul-one f (Field.finv f S))))))))

------------------------------------------------------------------------
-- The natural-number embedding.

natToField : (F : Set) → (f : Field F) → ℕ → F
natToField F f zero    = Field.fzero f
natToField F f (suc n) = Field.fplus f (natToField F f n) (Field.fone f)

natToField-suc : (F : Set) → (f : Field F) → (n : ℕ) →
  natToField F f (suc n) ≡
  Field.fplus f (natToField F f n) (Field.fone f)
natToField-suc F f n = refl

-- natToField (m + n) ≡ natToField m + natToField n
natToField-add : (F : Set) → (f : Field F) → (m n : ℕ) →
  natToField F f (m + n) ≡
  Field.fplus f (natToField F f m) (natToField F f n)
natToField-add F f zero n =
  sym (Field.zero-plus f (natToField F f n))
natToField-add F f (suc m) n =
  trans
    refl
    (trans
      (cong (λ x → Field.fplus f x (Field.fone f))
            (natToField-add F f m n))
      (trans
        (Field.plus-assoc f (natToField F f m) (natToField F f n) (Field.fone f))
        (trans
          (cong (λ x → Field.fplus f (natToField F f m) x)
                (Field.plus-comm f (natToField F f n) (Field.fone f)))
          (sym (Field.plus-assoc f (natToField F f m) (Field.fone f) (natToField F f n))))))

------------------------------------------------------------------------
-- Vector operations over a field.

-- Pointwise addition.
vadd : (F : Set) → (f : Field F) → (n : ℕ) → Vec F n → Vec F n → Vec F n
vadd F f zero v1 v2 = tt
vadd F f (suc n) (a , v1) (b , v2) =
  (Field.fplus f a b , vadd F f n v1 v2)

-- Pointwise scaling.
vscale : (F : Set) → (f : Field F) → (n : ℕ) → F → Vec F n → Vec F n
vscale F f zero c v = tt
vscale F f (suc n) c (a , v) =
  (Field.fmul f c a , vscale F f n c v)

-- Build a vector from its lookup function.
vecOfLookup : (F : Set) → (n : ℕ) → (Fin n → F) → Vec F n
vecOfLookup F zero g = tt
vecOfLookup F (suc n) g =
  (g (finZero n) , vecOfLookup F n (λ (k , e) → g (fsuc n (k , e))))

-- The only equality true ≡ true is refl.
true-refl : {e : true ≡ true} → e ≡ refl
true-refl {refl} = refl

-- vlookup (vecOfLookup n g) k ≡ g k
vecOfLookup-lookup : (F : Set) → (n : ℕ) → (g : Fin n → F) → (k : Fin n) →
  vlookup F n (vecOfLookup F n g) k ≡ g k
vecOfLookup-lookup F zero g i with i
vecOfLookup-lookup F zero g i | (k₀ , e) with k₀
vecOfLookup-lookup F zero g i | (k₀ , e) | zero with e
vecOfLookup-lookup F zero g i | (k₀ , e) | zero | ()
vecOfLookup-lookup F zero g i | (k₀ , e) | (suc k₁) with e
vecOfLookup-lookup F zero g i | (k₀ , e) | (suc k₁) | ()
vecOfLookup-lookup F (suc n) g k with k
vecOfLookup-lookup F (suc n) g k | (zero , e₀) =
  cong (λ x → g x) (sym (cong (λ x → zero , x) (true-refl {e₀})))
vecOfLookup-lookup F (suc n) g k | (suc k₁ , e₀) =
  vecOfLookup-lookup F n (λ (k , e) → g (fsuc n (k , e))) (k₁ , e₀)

-- Mapping a constant vector with g gives the constant g c vector.
vmap-const : (F : Set) → (n : ℕ) → (g : F → F) → (c : F) →
  vmap F F n g (vreplicate F n c) ≡ vreplicate F n (g c)
vmap-const F zero g c = refl
vmap-const F (suc n) g c =
  vec-eq-const F n (cong g refl) (vmap-const F n g c)

------------------------------------------------------------------------
-- The vector sum.

vsum : (F : Set) → (f : Field F) → (n : ℕ) → Vec F n → F
vsum F f zero v = Field.fzero f
vsum F f (suc n) (a , v) =
  Field.fplus f a (vsum F f n v)

-- vsum (v + w) ≡ vsum v + vsum w
vsum-vadd : (F : Set) → (f : Field F) → (n : ℕ) → (v w : Vec F n) →
  vsum F f n (vadd F f n v w) ≡
  Field.fplus f (vsum F f n v) (vsum F f n w)
vsum-vadd F f zero v1 v2 =
  sym (Field.zero-plus f (Field.fzero f))
vsum-vadd F f (suc n) (a , v1) (b , v2) =
  trans
    (Field.plus-assoc f a b (vsum F f n (vadd F f n v1 v2)))
    (trans
      (cong (λ x → Field.fplus f a (Field.fplus f b x))
            (vsum-vadd F f n v1 v2))
      (trans
        (cong (λ x → Field.fplus f a x)
              (sym (Field.plus-assoc f b (vsum F f n v1) (vsum F f n v2))))
        (trans
          (cong (λ x → Field.fplus f a x)
                (cong (λ y → Field.fplus f y (vsum F f n v2))
                      (Field.plus-comm f b (vsum F f n v1))))
          (trans
            (cong (λ x → Field.fplus f a x)
                  (Field.plus-assoc f (vsum F f n v1) b (vsum F f n v2)))
            (sym (Field.plus-assoc f a (vsum F f n v1)
                                   (Field.fplus f b (vsum F f n v2))))))))

-- vsum (c •ᵥ v) ≡ c * vsum v
vsum-vscale : (F : Set) → (f : Field F) → (n : ℕ) → (c : F) → (v : Vec F n) →
  vsum F f n (vscale F f n c v) ≡ Field.fmul f c (vsum F f n v)
vsum-vscale F f zero c v =
  sym (Field.mul-zero f c)
vsum-vscale F f (suc n) c (a , v) =
  trans
    (cong (λ x → Field.fplus f (Field.fmul f c a) x) (vsum-vscale F f n c v))
    (sym (Field.mul-distr f c a (vsum F f n v)))

-- vsum (const c) ≡ n ↦ c ... i.e. ≡ (natToField n) * c
vsum-const : (F : Set) → (f : Field F) → (n : ℕ) → (c : F) →
  vsum F f n (vreplicate F n c) ≡
  Field.fmul f (natToField F f n) c
vsum-const F f zero c =
  sym (trans (Field.mul-comm f (Field.fzero f) c)
             (Field.mul-zero f c))
vsum-const F f (suc n) c =
  trans
    (Field.plus-comm f c (vsum F f n (vreplicate F n c)))
    (trans
      (cong (λ x → Field.fplus f x c) (vsum-const F f n c))
      (trans
        (cong (λ x → Field.fplus f x c)
              (Field.mul-comm f (natToField F f n) c))
        (trans
          (cong (λ x → Field.fplus f (Field.fmul f c (natToField F f n)) x)
                (sym (Field.mul-one f c)))
          (trans
            (sym (Field.mul-distr f c (natToField F f n) (Field.fone f)))
            (sym (Field.mul-comm f (Field.fplus f (natToField F f n) (Field.fone f)) c))))))

-- vsum (v -ᵥ const c) ≡ vsum v - vsum (const c)
vsum-vfminus : (F : Set) → (f : Field F) → (n : ℕ) → (v : Vec F n) → (c : F) →
  vsum F f n (vadd F f n v
                    (vmap F F n (Field.fneg f) (vreplicate F n c))) ≡
  fminus F f (vsum F f n v) (vsum F f n (vreplicate F n c))
vsum-vfminus F f n v c =
  trans (vsum-vadd F f n v (vmap F F n (Field.fneg f) (vreplicate F n c)))
        (trans (cong (λ x → Field.fplus f (vsum F f n v) x) s1)
               (cong (λ x → Field.fplus f (vsum F f n v) x)
                     (cong (Field.fneg f) (sym (vsum-const F f n c)))))
  where
    -- vsum (vmap fneg (const c))  ≡  -(natToField n * c)
    s1 : vsum F f n (vmap F F n (Field.fneg f) (vreplicate F n c)) ≡
         Field.fneg f (Field.fmul f (natToField F f n) c)
    s1 =
      trans
        (cong (λ y → vsum F f n y) (vmap-const F n (Field.fneg f) c))
        (trans
          (vsum-const F f n (Field.fneg f c))
          (trans
            (Field.mul-comm f (natToField F f n) (Field.fneg f c))
            (trans
              (sym (neg-mul F f c (natToField F f n)))
              (sym (cong (Field.fneg f)
                         (Field.mul-comm f (natToField F f n) c))))))

------------------------------------------------------------------------
-- A (linear) order on a field.

-- NB: the order is a predicate (F → F → Set), so this record lives in
-- Set₁; every *element* it talks about is still in Set.
record Ordered (F : Set) (f : Field F) : Set₁ where
  field
    le             : F → F → Set
    le-refl        : (a : F) → le a a
    le-trans       : (a b c : F) → le a b → le b c → le a c
    le-total       : (a b : F) → le a b ∨ le b a
    le-rewrite     : (a b c : F) → a ≡ b → le a c → le b c
    le-rewrite-r   : (a b c : F) → a ≡ b → le c a → le c b
    add-mono       : (a b c : F) → le a b →
                     le (Field.fplus f a c) (Field.fplus f b c)
    mul-mono       : (a b c : F) → le a b →
                     le (Field.fzero f) c →
                     le (Field.fmul f a c) (Field.fmul f b c)
    nat-embed-mono : (m n : ℕ) → m ≤N n →
                     le (natToField F f m) (natToField F f n)
    zero-≤-one     : le (Field.fzero f) (Field.fone f)
    inv-pos        : (a : F) → a ≢ Field.fzero f →
                     le (Field.fzero f) a →
                     le (Field.fzero f) (Field.finv f a)

-- 0 ≤ natToField n
zero-nat : (F : Set) → (f : Field F) → (o : Ordered F f) → (n : ℕ) →
  Ordered.le o (Field.fzero f) (natToField F f n)
zero-nat F f o zero =
  Ordered.le-refl o (Field.fzero f)
zero-nat F f o (suc n) =
  Ordered.le-rewrite-r
    o
    (Field.fplus f (natToField F f n) (Field.fone f))
    (natToField F f (suc n))
    (Field.fzero f)
    (sym (natToField-suc F f n))
    (Ordered.le-trans
       o (Field.fzero f) (Field.fone f)
         (Field.fplus f (natToField F f n) (Field.fone f))
       (Ordered.zero-≤-one o) p1)
  where
    p0 : Ordered.le o
           (Field.fplus f (Field.fzero f) (Field.fone f))
           (Field.fplus f (natToField F f n) (Field.fone f))
    p0 =
      Ordered.add-mono o (Field.fzero f) (natToField F f n)
        (Field.fone f) (zero-nat F f o n)
    p1 : Ordered.le o
           (Field.fone f)
           (Field.fplus f (natToField F f n) (Field.fone f))
    p1 =
      Ordered.le-rewrite o
        (Field.fplus f (Field.fzero f) (Field.fone f))
        (Field.fone f)
        (Field.fplus f (natToField F f n) (Field.fone f))
        (Field.zero-plus f (Field.fone f)) p0

------------------------------------------------------------------------
-- An exponential structure on a field.

record Exp (F : Set) (f : Field F) : Set where
  field
    exp      : F → F
    exp-zero : exp (Field.fzero f) ≡ Field.fone f
    exp-plus : (a b : F) →
      exp (Field.fplus f a b) ≡ Field.fmul f (exp a) (exp b)

open Exp using (exp)

-- exp a ≠ 0
exp-neq-zero : (F : Set) → (f : Field F) → (e : Exp F f) → (a : F) →
  Exp.exp e a ≢ Field.fzero f
exp-neq-zero F f e a h =
  contradiction
    (trans
      (sym (trans (sym (Exp.exp-plus e a (Field.fneg f a)))
                  (trans (cong (Exp.exp e) (Field.plus-neg f a))
                         (Exp.exp-zero e))))
      (trans
        (cong (λ x → Field.fmul f x (Exp.exp e (Field.fneg f a))) h)
        (trans (Field.mul-comm f (Field.fzero f) (Exp.exp e (Field.fneg f a)))
               (Field.mul-zero f (Exp.exp e (Field.fneg f a))))))
    (λ e → Field.fzero≢fone f (sym e))

-- exp (neg a) ≡ inv (exp a)
exp-neg : (F : Set) → (f : Field F) → (e : Exp F f) → (a : F) →
  Exp.exp e (Field.fneg f a) ≡ Field.finv f (Exp.exp e a)
exp-neg F f e a =
  inv-unique F f (Exp.exp e a)
             (Exp.exp e (Field.fneg f a))
             (Field.finv f (Exp.exp e a))
    e1
    (Field.inv-ne f (Exp.exp e a) (exp-neq-zero F f e a))
  where
    e1 : Field.fmul f (Exp.exp e a) (Exp.exp e (Field.fneg f a)) ≡
         Field.fone f
    e1 =
      trans
        (sym (Exp.exp-plus e a (Field.fneg f a)))
        (trans (cong (Exp.exp e) (Field.plus-neg f a))
               (Exp.exp-zero e))

-- exp (a - b) ≡ exp a * inv (exp b)
exp-minus : (F : Set) → (f : Field F) → (e : Exp F f) → (a b : F) →
  Exp.exp e (fminus F f a b) ≡
  Field.fmul f (Exp.exp e a) (Field.finv f (Exp.exp e b))
exp-minus F f e a b =
  trans
    (Exp.exp-plus e a (Field.fneg f b))
    (cong (λ x → Field.fmul f (Exp.exp e a) x) (exp-neg F f e b))
