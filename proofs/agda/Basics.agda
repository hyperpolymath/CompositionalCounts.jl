------------------------------------------------------------------------
-- CompositionalCounts.jl — machine-checked algebraic claims.
--
-- Basics : the logical core used by every other module.
--
-- Built only on the Agda builtin modules (Nat, Bool, Equality, Sigma,
-- Unit). Everything in this module is proved from those; nothing is
-- postulated. No standard library is used anywhere in this
-- development (the CI gate typechecks with --no-libraries).
--
-- House style (enforced by review, required by the toolchain):
--   * every parameter of every signature is declared explicitly —
--     no reliance on implicit-parameter inference;
--   * every implicit parameter used in a clause body is named in the
--     clause head;
--   * single-universe (Set) typing throughout — every type in this
--     development lives in Set.
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module Basics where

open import Agda.Builtin.Nat      using (Nat ; zero ; suc ; _+_ ; _-_ ; _*_ ; _==_ ; _<_)
open import Agda.Builtin.Bool     using (Bool ; true ; false)
open import Agda.Builtin.Equality using (_≡_ ; refl)
open import Agda.Builtin.Sigma    using (Σ ; fst ; snd ; _,_)
open import Agda.Builtin.Unit     using (⊤ ; tt)

------------------------------------------------------------------------
-- The builtin natural numbers, with their usual alias.

ℕ = Nat

------------------------------------------------------------------------
-- Conditional (this build has no builtin if-then-else).

if : {A : Set} → Bool → A → A → A
if {A} true  a b = a
if {A} false a b = b

------------------------------------------------------------------------
-- Bottom, negation, disjunction, decidability.

data ⊥ : Set where

⊥-elim : {A : Set} → ⊥ → A
⊥-elim {A} ()

infix 3 ¬_
¬_ : Set → Set
¬ A = A → ⊥

contradiction : {A B : Set} → A → ¬ A → B
contradiction {A} {B} a ¬a = ⊥-elim {B} (¬a a)

infix 40 _≢_
_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

infixr 0 _∨_
data _∨_ (A B : Set) : Set where
  inl : A → A ∨ B
  inr : B → A ∨ B

[_,_] : {A B C : Set} → (A → C) → (B → C) → A ∨ B → C
[ f , g ] (inl a) = f a
[ f , g ] (inr b) = g b

data Dec (P : Set) : Set where
  yes : P → Dec P
  no  : ¬ P → Dec P

------------------------------------------------------------------------
-- The external product (constructor named `pair` so it cannot be
-- confused with the Σ-pair `_,_`).

infixr 4 _×_

data _×_ (A B : Set) : Set where
  pair : A → B → A × B

proj₁ : {A B : Set} → A × B → A
proj₁ (pair a b) = a

proj₂ : {A B : Set} → A × B → B
proj₂ (pair a b) = b

------------------------------------------------------------------------
-- Boolean operations (the builtin Bool carries no operations).

not : Bool → Bool
not true  = false
not false = true

infixr 3 _∧_
_∧_ : Bool → Bool → Bool
true  ∧ b = b
false ∧ _ = false

------------------------------------------------------------------------
-- Equality: the combinators for working with _≡_.

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym {A} {x} {y} refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans {A} {x} {y} {z} refl p = p

subst : {A : Set} (P : A → Set) {x y : A} → x ≡ y → P x → P y
subst {A} P {x} {y} refl p = p

cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong {A} {B} f {x} {y} refl = refl

cong₂ : {A B C : Set} (f : A → B → C) {x₁ x₂ : A} {y₁ y₂ : B} →
        x₁ ≡ x₂ → y₁ ≡ y₂ → f x₁ y₁ ≡ f x₂ y₂
cong₂ {A} {B} {C} f {x₁} {x₂} {y₁} {y₂} p q =
  trans (cong (λ a → f a y₁) p)
        (subst (λ a → f a y₁ ≡ f a y₂) p (cong (f x₁) q))

------------------------------------------------------------------------
-- Functions.

_∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
_∘_ {A} {B} {C} g f x = g (f x)

id : {A : Set} → A → A
id {A} a = a

const : {A B : Set} → A → B → A
const {A} {B} a b = a

flip : {A B C : Set} → (A → B → C) → B → A → C
flip {A} {B} {C} f b a = f a b
