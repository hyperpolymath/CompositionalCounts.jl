{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- CompositionalCounts.jl — machine-checked algebraic claims.
--
-- Nat : the strict order, the total order, and the arithmetic facts
-- about the builtin natural numbers, proved from the builtin
-- definitions.
--
-- The total order _≤N_ is encoded existentially (m ≤N n means "there
-- is a gap k with n ≡ m + k"); this keeps every type in Set and needs
-- no axioms.
--
-- House style (see Basics): single universe Set; every parameter
-- declared explicitly; every implicit parameter used in a clause
-- body named in the clause head; no forward references.
------------------------------------------------------------------------

module Nat where

open import Basics
open import Agda.Builtin.Nat      using (zero ; suc ; _+_ ; _*_)
open import Agda.Builtin.Bool     using (Bool ; true ; false)
open import Agda.Builtin.Equality using (_≡_ ; refl)
open import Agda.Builtin.Sigma    using (Σ ; fst ; snd ; _,_)

------------------------------------------------------------------------
-- The strict order as a boolean, and the (total) order as a
-- proposition.

_<?>_ : ℕ → ℕ → Bool
_<?>_ zero zero     = false
_<?>_ zero (suc n)  = true
_<?>_ (suc n) zero  = false
_<?>_ (suc n) (suc m) = _<?>_ n m

-- The total order: m ≤N n  :=  ∃ k , n ≡ m + k.

_≤N_ : ℕ → ℕ → Set
m ≤N n = Σ ℕ (λ k → n ≡ m + k)

infix 4 _≤N_

_≥N_ : ℕ → ℕ → Set
m ≥N n = n ≤N m

-- The strict order.

_<N_ : ℕ → ℕ → Set
m <N n = suc m ≤N n

infix 4 _<N_

------------------------------------------------------------------------
-- Addition, first-argument recursion style.

+-zero-r : (m : ℕ) → m + zero ≡ m
+-zero-r zero    = refl
+-zero-r (suc m) = cong suc (+-zero-r m)

-- n + suc m ≡ suc (n + m)
+-suc-r : (n m : ℕ) → n + suc m ≡ suc (n + m)
+-suc-r zero m   = refl
+-suc-r (suc n) m = cong suc (+-suc-r n m)

-- m + 1 ≡ suc m
m-plus-one : (m : ℕ) → m + 1 ≡ suc m
m-plus-one zero   = refl
m-plus-one (suc m) = cong suc (m-plus-one m)

+-comm : (m n : ℕ) → m + n ≡ n + m
+-comm zero n = sym (+-zero-r n)
+-comm (suc m) n =
  trans (cong suc (+-comm m n)) (sym (+-suc-r n m))

+-assoc : (a b c : ℕ) → a + b + c ≡ a + (b + c)
+-assoc zero b c    = refl
+-assoc (suc a) b c = cong suc (+-assoc a b c)

-- a + (b + c) ≡ b + (a + c)
+-shuffle2 : (a b c : ℕ) → a + (b + c) ≡ b + (a + c)
+-shuffle2 a b c =
  trans (sym (+-assoc a b c))
        (trans (cong (λ x → x + c) (+-comm a b))
               (+-assoc b a c))

-- (a + b) + (c + d) ≡ (a + c) + (b + d)
+-shuffle4 : (a b c d : ℕ) → (a + b) + (c + d) ≡ (a + c) + (b + d)
+-shuffle4 a b c d =
  trans (+-assoc a b (c + d))
        (trans (cong (λ y → a + y) (sym (+-assoc b c d)))
          (trans (cong (λ y → a + y)
                       (trans (+-assoc b c d) (+-shuffle2 b c d)))
                 (sym (+-assoc a c (b + d)))))

------------------------------------------------------------------------
-- Successor injection and cancellation lemmas.

suc-inj : {x y : ℕ} → suc x ≡ suc y → x ≡ y
suc-inj refl = refl

-- x + k ≡ y + k  →  x ≡ y
+-canc-r : {x y : ℕ} {k : ℕ} → x + k ≡ y + k → x ≡ y
+-canc-r {x} {y} {zero} e = trans (sym (+-zero-r x)) (trans e (+-zero-r y))
+-canc-r {x} {y} {suc k} e =
  +-canc-r {x} {y} {k}
    (suc-inj (trans (sym (+-suc-r x k)) (trans e (+-suc-r y k))))

-- m + x ≡ m + y  →  x ≡ y
+-canc-l : {m x y : ℕ} → m + x ≡ m + y → x ≡ y
+-canc-l {m} {x} {y} e with m
+-canc-l {m} {x} {y} e | zero   = e
+-canc-l {m} {x} {y} e | (suc w) = +-canc-l {w} {x} {y} (suc-inj e)

-- n ≡ n + X  →  X ≡ 0
+-canc-l-0 : {n X : ℕ} → n ≡ n + X → X ≡ zero
+-canc-l-0 {n} {X} e with n
+-canc-l-0 {n} {X} e | zero   = sym e
+-canc-l-0 {n} {X} e | (suc w) = +-canc-l-0 {w} {X} (suc-inj e)

-- l + k ≡ 0  →  l ≡ 0 and k ≡ 0
+-zero-sum : (l k : ℕ) → l + k ≡ zero → Σ (l ≡ zero) (λ _ → k ≡ zero)
+-zero-sum zero k e = (refl , e)
+-zero-sum (suc l) k e with e
+-zero-sum (suc l) k e | ()

-- 0 ≡ n + l  →  n ≡ 0 and l ≡ 0
+-zero-sum-r : {n l : ℕ} → zero ≡ n + l → Σ (n ≡ zero) (λ _ → l ≡ zero)
+-zero-sum-r {zero} {l} e = (refl , sym e)
+-zero-sum-r {suc n} {l} e with e
+-zero-sum-r {suc n} {l} e | ()

------------------------------------------------------------------------
-- Properties of the total order.

≤N-refl : (m : ℕ) → m ≤N m
≤N-refl m = (zero , sym (+-zero-r m))

≤N-trans : {m n p : ℕ} → m ≤N n → n ≤N p → m ≤N p
≤N-trans {m} {n} {p} (k , e1) (l , e2) =
  (k + l , trans e2 (trans (cong (λ x → x + l) e1) (+-assoc m k l)))

-- n ≤N m  →  n ≤N suc m
right-lift : {n m : ℕ} → n ≤N m → n ≤N suc m
right-lift {n} {m} (k , e) =
  (k + 1 , trans (sym (m-plus-one m))
                 (trans (cong (λ x → x + 1) e) (+-assoc n k 1)))

-- m ≤N n  →  suc m ≤N suc n
suc-lift : {m n : ℕ} → m ≤N n → suc m ≤N suc n
suc-lift {m} {n} (k , e) =
  (k , trans (sym (m-plus-one n))
             (trans (cong (λ x → x + 1) e) (m-plus-one (m + k))))

≤N-total : (m n : ℕ) → m ≤N n ∨ n ≤N m
≤N-total zero n          = inl (n , refl)
≤N-total (suc m) zero    = inr (suc m , refl)
≤N-total (suc m) (suc n) with ≤N-total m n
≤N-total (suc m) (suc n) | inl q = inl (suc-lift q)
≤N-total (suc m) (suc n) | inr q = inr (suc-lift q)

-- ¬(m ≡ suc (m + k))
no-suc-self-raw : (m k : ℕ) → ¬ (m ≡ suc (m + k))
no-suc-self-raw zero k e with e
no-suc-self-raw zero k e | ()
no-suc-self-raw (suc m) k e = no-suc-self-raw m k (suc-inj e)

≤N-antisym : {m n : ℕ} → m ≤N n → n ≤N m → m ≡ n
≤N-antisym {zero} {n} (k , e1) (l , e2) =
  sym (fst (+-zero-sum-r {n} {l} e2))
≤N-antisym {suc m} {n} (k , e1) (zero , e2) =
  let k0 = +-canc-l-0 {suc m} {k} (trans (trans e2 (+-zero-r n)) e1)
  in sym (trans e1 (cong suc (trans (cong (λ y → m + y) k0) (+-zero-r m))))
≤N-antisym {suc m} {n} (k , e1) (suc l , e2) =
  ⊥-elim {suc m ≡ n}
    (no-suc-self-raw m (k + l)
      (trans (suc-inj
              (trans e2
                     (trans (cong (λ x → x + suc l) e1)
                            (cong suc (+-suc-r (m + k) l)))))
             (cong suc (+-assoc m k l))))

no-suc≤0 : (m : ℕ) → ¬ (suc m ≤N zero)
no-suc≤0 m (k , e) with e
no-suc≤0 m (k , e) | ()

no-suc-self : (m : ℕ) → ¬ (suc m ≤N m)
no-suc-self m (k , e) = no-suc-self-raw m k e

-- The strict order is irreflexive.
lt-irr : {a : ℕ} → ¬ (a <N a)
lt-irr {a} (k , e) = no-suc-self a (k , e)

-- Trichotomy-lite:  m ≤N n  implies  m ≡ n  or  m <N n.
≤N-cmp : (m n : ℕ) → m ≤N n → m ≡ n ∨ m <N n
≤N-cmp zero zero (zero , e) = inl (trans (sym e) (sym (+-zero-r zero)))
≤N-cmp zero (suc n) (k , e) = inr (n , refl)
≤N-cmp (suc m) zero (k , e) with e
≤N-cmp (suc m) zero (k , e) | ()
≤N-cmp (suc m) (suc n) (k , e) with k
≤N-cmp (suc m) (suc n) (k , e) | zero =
  inl (cong suc (sym (trans (suc-inj e) (+-zero-r m))))
≤N-cmp (suc m) (suc n) (k , e) | (suc k₁) =
  inr (k₁ , trans e (cong suc (+-suc-r m k₁)))

-- m <N n  ⇒  m ≤N n   (from  m <N n  =  suc m ≤N n)
≤N-from-lt : (m n : ℕ) → m <N n → m ≤N n
≤N-from-lt m n (k , e) =
  (1 + k , trans e (trans (cong (λ x → x + k) (sym (m-plus-one m)))
                         (+-assoc m 1 k)))

-- m ≡ n  →  m ≤N n
≤N-from-eq : (m n : ℕ) → m ≡ n → m ≤N n
≤N-from-eq m n e = (zero , trans (sym e) (sym (+-zero-r m)))

natLeq? : (m n : ℕ) → Dec (m ≤N n)
natLeq? zero n          = yes (n , refl)
natLeq? (suc m) zero    = no (no-suc≤0 m)
natLeq? (suc m) (suc n) with natLeq? m n
natLeq? (suc m) (suc n) | yes (k , e) = yes (k , cong suc e)
natLeq? (suc m) (suc n) | no  ¬ih     =
  no (λ (k , e) → ¬ih (k , suc-inj e))

natLt? : (m n : ℕ) → Dec (m <N n)
natLt? m n = natLeq? (suc m) n

natEq? : (m n : ℕ) → Dec (m ≡ n)
natEq? m n with natLeq? m n
natEq? m n | yes q with natLeq? n m
natEq? m n | yes q | yes r = yes (≤N-antisym q r)
natEq? m n | yes q | no  ¬r = no (λ e → ¬r (≤N-from-eq n m (sym e)))
natEq? m n | no  ¬q         = no (λ e → ¬q (≤N-from-eq m n e))

------------------------------------------------------------------------
-- Multiplication, first-argument recursion style.

-- m * (suc n) ≡ m + m * n
*-suc : (m n : ℕ) → m * (suc n) ≡ m + m * n
*-suc zero n = refl
*-suc (suc m) n =
  trans (cong suc (cong (λ y → n + y) (*-suc m n)))
        (cong suc (+-shuffle2 n m (m * n)))

-- n * 0 ≡ 0
*-zero-r : (n : ℕ) → n * zero ≡ zero
*-zero-r zero   = refl
*-zero-r (suc n) = *-zero-r n

-- (n + p) * m ≡ n * m + p * m
*-distr-r : (n p m : ℕ) → (n + p) * m ≡ n * m + p * m
*-distr-r n p zero =
  trans (*-zero-r (n + p))
        (trans (sym (*-zero-r p))
               (cong (λ y → y + p * zero) (sym (*-zero-r n))))
*-distr-r n p (suc m) =
  trans (*-suc (n + p) m)
        (trans (cong (λ y → (n + p) + y) (*-distr-r n p m))
               (trans (+-shuffle4 n p (n * m) (p * m))
                      (trans (cong (λ y → y + (p + p * m)) (sym (*-suc n m)))
                             (cong (λ y → n * (suc m) + y)
                                   (sym (*-suc p m))))))

-- a * b * c ≡ a * (b * c)
*-assoc : (a b c : ℕ) → a * b * c ≡ a * (b * c)
*-assoc zero b c = refl
*-assoc (suc a) b c =
  trans (*-distr-r b (a * b) c)
        (cong (λ y → b * c + y) (*-assoc a b c))

-- m * n ≡ n * m
*-comm : (m n : ℕ) → m * n ≡ n * m
*-comm m zero   = *-zero-r m
*-comm m (suc n) =
  trans (*-suc m n) (cong (λ y → m + y) (*-comm m n))

-- 2 * m ≡ m + m
double-equiv : (m : ℕ) → 2 * m ≡ m + m
double-equiv m rewrite +-zero-r m = refl

-- Strict-order facts.

-- The boolean test is sound: _<?>_ k n ≡ true  →  k <N n.
<?-sound : {k n : ℕ} → _<?>_ k n ≡ true → k <N n
<?-sound {zero} {zero} e with e
<?-sound {zero} {zero} e | ()
<?-sound {zero} {suc n} e = (n , refl)
<?-sound {suc k} {zero} e with e
<?-sound {suc k} {zero} e | ()
<?-sound {suc k} {suc n} e = suc-lift (<?-sound {k} {n} e)

-- a <? a is never true.
<?-irr-bool : {a : ℕ} → ¬ (_<?>_ a a ≡ true)
<?-irr-bool {zero} e with e
<?-irr-bool {zero} e | ()
<?-irr-bool {suc a} e = <?-irr-bool {a} e

-- a <? b  →  ¬ (b <? a)
<?-irr : {a b : ℕ} → _<?>_ a b ≡ true → ¬ (_<?>_ b a ≡ true)
<?-irr {a} {b} e1 e2 =
  no-suc-self a
    (≤N-trans (<?-sound e1)
              (≤N-trans (right-lift (≤N-refl b)) (<?-sound e2)))

-- a <? b  →  a <? suc b
<?-mono-r : {a b : ℕ} → _<?>_ a b ≡ true → _<?>_ a (suc b) ≡ true
<?-mono-r {zero} {b} e = refl
<?-mono-r {suc a} {zero} e with e
<?-mono-r {suc a} {zero} e | ()
<?-mono-r {suc a} {suc b} e = <?-mono-r {a} {b} e

-- Transitivity of the strict order.
lt-trans : (m n p : ℕ) → m <N n → n <N p → m <N p
lt-trans m n p (k₁ , e₁) (k₂ , e₂) =
  ≤N-trans (k₁ , e₁)
           (1 + k₂ , trans e₂
                          (trans (cong (λ x → x + k₂) (sym (m-plus-one n)))
                                 (+-assoc n 1 k₂)))

-- Substitution for the right-hand side of the strict order.
<N-subst-r : {x y z : ℕ} → y ≡ z → x <N y → x <N z
<N-subst-r {x} {y} {z} e₀ (k , e₁) =
  (k , trans (sym e₀) e₁)

-- _<?>_ a b ≡ true  →  suc a ≤N b
<?-step : {a b : ℕ} → _<?>_ a b ≡ true → suc a ≤N b
<?-step {zero} {zero} e with e
<?-step {zero} {zero} e | ()
<?-step {zero} {suc b} e = (b , refl)
<?-step {suc a} {zero} e with e
<?-step {suc a} {zero} e | ()
<?-step {suc a} {suc b} e with <?-step {a} {b} e
<?-step {suc a} {suc b} e | (zero , eq) = (zero , cong suc eq)
<?-step {suc a} {suc b} e | (suc d₁ , eq) = (suc d₁ , cong suc eq)

-- a <? suc a   (the boolean test of a < a+1)
<?-lt-suc-bool : (a : ℕ) → _<?>_ a (suc a) ≡ true
<?-lt-suc-bool zero    = refl
<?-lt-suc-bool (suc a) = <?-lt-suc-bool a

-- a <N b  →  a <? b   (the boolean test is complete for the order)
<?-complete : (a b : ℕ) → a <N b → _<?>_ a b ≡ true
<?-complete a b (j , e) with a
<?-complete a b (j , e) | zero with b
<?-complete a b (j , e) | zero | zero with e
<?-complete a b (j , e) | zero | zero | ()
<?-complete a b (j , e) | zero | (suc n) = refl
<?-complete a b (j , e) | (suc a₁) with b
<?-complete a b (j , e) | (suc a₁) | zero with e
<?-complete a b (j , e) | (suc a₁) | zero | ()
<?-complete a b (j , e) | (suc a₁) | (suc b₁) with j
<?-complete a b (j , e) | (suc a₁) | (suc b₁) | zero =
  trans (cong (λ x → _<?>_ a₁ x) e0) (<?-lt-suc-bool a₁)
  where
    -- e : suc b₁ ≡ suc (suc a₁) + 0 = suc (suc (a₁ + 0))
    e0 : b₁ ≡ suc a₁
    e0 = trans (suc-inj e) (cong suc (+-zero-r a₁))
<?-complete a b (j , e) | (suc a₁) | (suc b₁) | (suc j₁) =
  <?-complete a₁ b₁ (suc j₁ , e0)
  where
    -- e : suc b₁ ≡ suc (suc a₁) + suc j₁ = suc (suc a₁ + suc j₁)
    e0 : b₁ ≡ suc a₁ + suc j₁
    e0 = suc-inj e

-- a <? suc b  →  a ≤N b
<?-lt-suc : {a b : ℕ} → _<?>_ a (suc b) ≡ true → a ≤N b
<?-lt-suc {zero} {b} e = (b , refl)
<?-lt-suc {suc a} {b} e = <?-step {a} {b} e

-- m * a ≤N n * a  when  m ≤N n
*-mono-l : (m n a : ℕ) → m ≤N n → m * a ≤N n * a
*-mono-l m n a (d , e) =
  (d * a , trans (cong (λ y → y * a) e) (*-distr-r m d a))

------------------------------------------------------------------------
-- Substitution for order and equality.

≤N-subst : {m n p : ℕ} → m ≡ n → m ≤N p → n ≤N p
≤N-subst refl q = q

≤N-subst-p : {m n p : ℕ} → n ≡ p → m ≤N n → m ≤N p
≤N-subst-p refl q = q

-- x ≡ y  →  x <N z  →  y <N z
<N-subst-l : {x y z : ℕ} → x ≡ y → x <N z → y <N z
<N-subst-l {x} {y} {z} e (j , q) =
  (j , trans q (cong suc (cong (λ x → x + j) e)))
