module Integer.Signed where

open import Data.Empty as ⊥
open import Data.Product as Σ
open import Data.Product.Relation.Pointwise.NonDependent
open import Data.Sum as ⊎
open import Data.Unit as ⊤
open import Equality
open import Function
open import Natural as ℕ
open import Quotient as /
open import Relation.Binary
open import Syntax

open Equality.FunctionProperties

⟦ℤ⟧ = ℕ ⊎ ℕ
⟦ℤ²⟧ = ⟦ℤ⟧ × ⟦ℤ⟧

infix 10 +1*_ -1*_
pattern +1*_ x = inj₁ x
pattern -1*_ x = inj₂ x

infix 1 _≈_
_≈_ : ⟦ℤ⟧ → ⟦ℤ⟧ → Set
+1* x ≈ +1* y = x ≡ y
+1* x ≈ -1* y = x ≡ 0 × y ≡ 0
-1* x ≈ +1* y = x ≡ 0 × y ≡ 0
-1* x ≈ -1* y = x ≡ y

≈-refl : ∀ {x} → x ≈ x
≈-refl {+1* x} = refl
≈-refl { -1* x} = refl

≈-sym : ∀ {x y} → x ≈ y → y ≈ x
≈-sym {+1* x} {+1* y} = sym
≈-sym {+1* x} { -1* y} = Σ.swap
≈-sym { -1* x} {+1* y} = Σ.swap
≈-sym { -1* x} { -1* y} = sym

≈-trans : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z
≈-trans {+1* x} {+1* y} {+1* z} p q = compPath p q
≈-trans {+1* x} {+1* y} { -1* z} p (q , r) = p ≫ q , r
≈-trans {+1* x} { -1* y} {+1* z} (p , q) (r , s) = p ≫ sym s
≈-trans {+1* x} { -1* y} { -1* z} (p , q) r = p , sym r ≫ q
≈-trans { -1* x} {+1* y} {+1* z} (p , q) r = p , sym r ≫ q
≈-trans { -1* x} {+1* y} { -1* z} (p , q) (r , s) = p ≫ sym s
≈-trans { -1* x} { -1* y} {+1* z} p (q , r) = p ≫ q , r
≈-trans { -1* x} { -1* y} { -1* z} p q = compPath p q

ℤ = ⟦ℤ⟧ / _≈_
ℤ² = ⟦ℤ²⟧ / Pointwise _≈_ _≈_

instance
  ⟦ℤ⟧-Number : Number ⟦ℤ⟧
  ⟦ℤ⟧-Number = record { Constraint = λ _ → ⊤ ; fromNat = λ n → +1* n }

  ℤ-Number : Number ℤ
  ℤ-Number = record { Constraint = λ _ → ⊤ ; fromNat = λ n → ⟦ fromNat n ⟧ }

  ⟦ℤ⟧-Negative : Negative ⟦ℤ⟧
  ⟦ℤ⟧-Negative = record { Constraint = λ _ → ⊤ ; fromNeg = λ n → -1* n }

  ℤ-Negative : Negative ℤ
  ℤ-Negative = record { Constraint = λ _ → ⊤ ; fromNeg = λ n → ⟦ fromNeg n ⟧ }

⟦negate⟧ : ⟦ℤ⟧ → ⟦ℤ⟧
⟦negate⟧ (+1* n) = -1* n
⟦negate⟧ (-1* n) = +1* n

negate : ℤ → ℤ
negate =
  ⟦negate⟧ // λ where
    (+1* x) (+1* y) → id
    (+1* x) (-1* y) → id
    (-1* x) (+1* y) → id
    (-1* x) (-1* y) → id

ℕ-minus : ℕ → ℕ → ⟦ℤ⟧
ℕ-minus zero n = -1* n
ℕ-minus m zero = +1* m
ℕ-minus (suc m) (suc n) = ℕ-minus m n

instance
  ℕ-minus-syntax : minus-syntax-simple ℕ ℕ ⟦ℤ⟧
  ℕ-minus-syntax = λ where ._-_ → ℕ-minus

ℕ-minus-identityˡ : ∀ a → ℕ-minus 0 a ≈ -1* a
ℕ-minus-identityˡ a = refl

ℕ-minus-identityʳ : ∀ a → ℕ-minus a 0 ≈ +1* a
ℕ-minus-identityʳ zero = refl , refl
ℕ-minus-identityʳ (suc a) = refl

⟦plus⟧ : ⟦ℤ²⟧ → ⟦ℤ⟧
⟦plus⟧ (+1* a , +1* b) = +1* (a + b)
⟦plus⟧ (+1* a , -1* b) = a - b
⟦plus⟧ (-1* a , +1* b) = b - a
⟦plus⟧ (-1* a , -1* b) = -1* (a + b)

plus : ℤ² → ℤ
plus =
  ⟦plus⟧ // λ where
    (+1* a , +1* b) (+1* c , +1* d) (p , q) → cong₂ _+_ p q
    (+1* a , +1* b) (+1* c , -1* d) (p , (q , r)) →
      case ⟪ p ⟫ ,′ ⟪ q ⟫ ,′ ⟪ r ⟫ of λ where
        (♥ , ♥ , ♥) →
          ≈-trans
            (⟨ ℕ.+-identityʳ a ⟩)
            (≈-sym (ℕ-minus-identityʳ a))
    (+1* a , +1* b) (-1* c , +1* d) ((p , q) , r) →
      case ⟪ p ⟫ ,′ ⟪ q ⟫ ,′ ⟪ r ⟫ of λ where
        (♥ , ♥ , ♥) →
          ≈-sym (ℕ-minus-identityʳ b)
    (+1* a , +1* b) (-1* c , -1* d) ((p , q) , (r , s)) →
      case ⟪ p ⟫ ,′ ⟪ q ⟫ ,′ ⟪ r ⟫ ,′ ⟪ s ⟫ of λ where
        (♥ , ♥ , ♥ , ♥) →
          refl , refl
    (+1* a , -1* b) (+1* c , +1* d) (p , (q , r)) →
      case ⟪ p ⟫ ,′ ⟪ q ⟫ ,′ ⟪ r ⟫ of λ where
        (♥ , ♥ , ♥) →
          ≈-trans {ℕ-minus a 0} {+1* a} {+1* (a + 0)}
            (ℕ-minus-identityʳ a)
            (sym ⟨ ℕ.+-identityʳ a ⟩)
    (+1* a , -1* b) (+1* c , -1* d) (p , q) →
      case ⟪ p ⟫ ,′ ⟪ q ⟫ of λ where
        (♥ , ♥) →
          ≈-refl
    (+1* a , -1* b) (-1* c , +1* d) ((p , q) , (r , s)) →
      case ⟪ p ⟫ ,′ ⟪ q ⟫ ,′ ⟪ r ⟫ ,′ ⟪ s ⟫ of λ where
        (♥ , ♥ , ♥ , ♥) →
          refl
    (+1* a , -1* b) (-1* c , -1* d) ((p , q) , r) →
      case ⟪ p ⟫ ,′ ⟪ q ⟫ ,′ ⟪ r ⟫ of λ where
        (♥ , ♥ , ♥) →
          refl
    (-1* a , +1* b) (+1* c , +1* d) ((p , q) , r) →
      case ⟪ p ⟫ ,′ ⟪ q ⟫ ,′ ⟪ r ⟫ of λ where
        (♥ , ♥ , ♥) →
          ℕ-minus-identityʳ b
    (-1* a , +1* b) (+1* c , -1* d) ((p , q) , (r , s)) →
      case ⟪ p ⟫ ,′ ⟪ q ⟫ ,′ ⟪ r ⟫ ,′ ⟪ s ⟫ of λ where
        (♥ , ♥ , ♥ , ♥) →
          refl
    (-1* a , +1* b) (-1* c , +1* d) (p , q) →
      case ⟪ p ⟫ ,′ ⟪ q ⟫ of λ where
        (♥ , ♥) →
          ≈-refl
    (-1* a , +1* b) (-1* c , -1* d) (p , (q , r)) →
      case ⟪ p ⟫ ,′ ⟪ q ⟫ ,′ ⟪ r ⟫ of λ where
        (♥ , ♥ , ♥) →
          sym ⟨ ℕ.+-identityʳ a ⟩
    (-1* a , -1* b) (+1* c , +1* d) ((p , q) , (r , s)) →
      case ⟪ p ⟫ ,′ ⟪ q ⟫ ,′ ⟪ r ⟫ ,′ ⟪ s ⟫ of λ where
        (♥ , ♥ , ♥ , ♥) →
          refl , refl
    (-1* a , -1* b) (+1* c , -1* d) ((p , q) , r) →
      case ⟪ p ⟫ ,′ ⟪ q ⟫ ,′ ⟪ r ⟫ of λ where
        (♥ , ♥ , ♥) →
          refl
    (-1* a , -1* b) (-1* c , +1* d) (p , (q , r)) →
      case ⟪ p ⟫ ,′ ⟪ q ⟫ ,′ ⟪ r ⟫ of λ where
        (♥ , ♥ , ♥) →
          ⟨ ℕ.+-identityʳ a ⟩
    (-1* a , -1* b) (-1* c , -1* d) (p , q) →
      case ⟪ p ⟫ ,′ ⟪ q ⟫ of λ where
        (♥ , ♥) →
          refl

⟦times⟧ : ⟦ℤ²⟧ → ⟦ℤ⟧
⟦times⟧ (+1* a , +1* b) = +1* (a * b)
⟦times⟧ (+1* a , -1* b) = -1* (a * b)
⟦times⟧ (-1* a , +1* b) = -1* (a * b)
⟦times⟧ (-1* a , -1* b) = +1* (a * b)

times : ℤ² → ℤ
times =
  ⟦times⟧ // λ where
    (+1* a , +1* b) (+1* c , +1* d) (p , q) → cong₂ _*_ p q
    (+1* a , -1* b) (+1* c , -1* d) (p , q) → cong₂ _*_ p q
    (-1* a , +1* b) (-1* c , +1* d) (p , q) → cong₂ _*_ p q
    (-1* a , -1* b) (-1* c , -1* d) (p , q) → cong₂ _*_ p q
    (+1* a , +1* b) (+1* c , -1* d) (p , q , r) →
      case ⟪ q ⟫ ,′ ⟪ r ⟫ of λ where
        (♥ , ♥) → ⟨ *-zeroʳ a ⟩ , ⟨ *-zeroʳ c ⟩
    (+1* a , -1* b) (+1* c , +1* d) (p , (q , r)) →
      case ⟪ q ⟫ ,′ ⟪ r ⟫ of λ where
        (♥ , ♥) → ⟨ *-zeroʳ a ⟩ , ⟨ *-zeroʳ c ⟩
    (-1* a , +1* b) (-1* c , -1* d) (p , (q , r)) →
      case ⟪ q ⟫ ,′ ⟪ r ⟫ of λ where
        (♥ , ♥) → ⟨ *-zeroʳ a ⟩ , ⟨ *-zeroʳ c ⟩
    (-1* a , -1* b) (-1* c , +1* d) (p , (q , r)) →
      case ⟪ q ⟫ ,′ ⟪ r ⟫ of λ where
        (♥ , ♥) → ⟨ *-zeroʳ a ⟩ , ⟨ *-zeroʳ c ⟩
    (+1* a , +1* b) (-1* c , +1* d) ((p , q) , r) →
      case ⟪ p ⟫ ,′ ⟪ q ⟫ of λ where
        (♥ , ♥) → refl , refl
    (+1* a , -1* b) (-1* c , -1* d) ((p , q) , r) →
      case ⟪ p ⟫ ,′ ⟪ q ⟫ of λ where
        (♥ , ♥) → refl , refl
    (-1* a , +1* b) (+1* c , +1* d) ((p , q) , r) →
      case ⟪ p ⟫ ,′ ⟪ q ⟫ of λ where
        (♥ , ♥) → refl , refl
    (-1* a , -1* b) (+1* c , -1* d) ((p , q) , r) →
      case ⟪ p ⟫ ,′ ⟪ q ⟫ of λ where
        (♥ , ♥) → refl , refl
    (+1* a , +1* b) (-1* c , -1* d) ((p , q) , r) →
      case ⟪ p ⟫ ,′ ⟪ q ⟫ of λ where
        (♥ , ♥) → refl
    (+1* a , -1* b) (-1* c , +1* d) ((p , q) , r) →
      case ⟪ p ⟫ ,′ ⟪ q ⟫ of λ where
        (♥ , ♥) → refl
    (-1* a , +1* b) (+1* c , -1* d) ((p , q) , r) →
      case ⟪ p ⟫ ,′ ⟪ q ⟫ of λ where
        (♥ , ♥) → refl
    (-1* a , -1* b) (+1* c , +1* d) ((p , q) , r) →
      case ⟪ p ⟫ ,′ ⟪ q ⟫ of λ where
        (♥ , ♥) → refl

instance
  ℤ-plus-syntax : plus-syntax-simple ℤ ℤ ℤ
  ℤ-plus-syntax = λ where ._+_ → /.uncurry ≈-refl ≈-refl plus

  ℤ-minus-syntax : minus-syntax-simple ℤ ℤ ℤ
  ℤ-minus-syntax = λ where ._-_ x y → x + negate y

  ℤ-times-syntax : times-syntax-simple ℤ ℤ ℤ
  ℤ-times-syntax = λ where ._*_ → /.uncurry ≈-refl ≈-refl times
