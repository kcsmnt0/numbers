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

ℤ = ⟦ℤ⟧ / _≈_
ℤ² = ⟦ℤ²⟧ / Pointwise _≈_ _≈_

⟦times⟧ : ⟦ℤ²⟧ → ⟦ℤ⟧
⟦times⟧ (+1* x , +1* y) = +1* (x * y)
⟦times⟧ (+1* x , -1* y) = -1* (x * y)
⟦times⟧ (-1* x , +1* y) = -1* (x * y)
⟦times⟧ (-1* x , -1* y) = +1* (x * y)

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
  ℤ-times-syntax : times-syntax-simple ℤ ℤ ℤ
  ℤ-times-syntax = λ where ._*_ → /.uncurry ≈-refl ≈-refl times
