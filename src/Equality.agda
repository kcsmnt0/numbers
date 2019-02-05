{-# OPTIONS --cubical #-}

module Equality where

import Algebra.FunctionProperties
import Algebra.Structures
open import Cubical.Core.Everything public hiding (module Σ)
open import Data.Empty
open import Data.Nat as ℕ
open import Data.Nat.Properties
open import Data.Product as Σ
open import Data.Unit
open import Function
open import Quotient
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as ♥ public using () renaming (refl to ♥)

open module FunctionProperties {a} {A : Set a} =
  Algebra.FunctionProperties {A = A} _≡_

open module Structures {a} {A : Set a} =
  Algebra.Structures {A = A} _≡_

coe : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A → B
coe = subst id

infix 1 _$⃗_
_$⃗_ : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A → B
_$⃗_ = coe

infix 1 _$⃖_
_$⃖_ : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → B → A
p $⃖ x = sym p $⃗ x

≡-isEquivalence : ∀ {ℓ} {A : Set ℓ} → IsEquivalence {A = A} _≡_
≡-isEquivalence = record
  { refl = refl
  ; sym = sym
  ; trans = compPath
  }

≡-isPreorder : ∀ {ℓ} {A : Set ℓ} → IsPreorder {A = A} _≡_ _≡_
≡-isPreorder = record
  { isEquivalence = ≡-isEquivalence
  ; reflexive = id
  ; trans = compPath
  }

module _ {ℓ} {A : Set ℓ} {a b : A} where
  ⟨_⟩ : a ♥.≡ b → a ≡ b
  ⟨ ♥ ⟩ = refl

  ⟪_⟫ : a ≡ b → a ♥.≡ b
  ⟪_⟫ = J (λ x _ → _ ♥.≡ x) ♥

infixl 5 _≫_
_≫_ : ∀ {ℓ} {A : Set ℓ} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
_≫_ = compPath

module _ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {f f′ : A → B} where
  happly : ∀ a → f ≡ f′ → f a ≡ f′ a
  happly a = cong λ g → g a

  congApp : ∀ {a a′} → f ≡ f′ → a ≡ a′ → f a ≡ f′ a′
  congApp p q = compPath (happly _ p) (cong f′ q)

cong₂ : ∀
  {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
  {a a′} {b b′}
  (f : A → B → C) →
  a ≡ a′ → b ≡ b′ →
  f a b ≡ f a′ b′
cong₂ f p q = congApp (cong f p) q
