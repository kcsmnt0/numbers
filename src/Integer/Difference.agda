module Integer.Difference where

open import Data.Product as Σ
open import Data.Product.Relation.Pointwise.NonDependent
open import Data.Unit
open import Equality
open import Natural as ℕ
open import Quotient as /
open import Relation.Binary
open import Syntax

infixl 6 _–_
pattern _–_ a b = _,_ a b

⟦ℤ⟧ = ℕ × ℕ
⟦ℤ²⟧ = ⟦ℤ⟧ × ⟦ℤ⟧

_≈_ : ⟦ℤ⟧ → ⟦ℤ⟧ → Set
(a – b) ≈ (c – d) = a + d ≡ c + b

≈-refl : ∀ {x} → x ≈ x
≈-refl = refl

ℤ = ⟦ℤ⟧ / _≈_
ℤ² = ⟦ℤ²⟧ / Pointwise _≈_ _≈_

instance
  ℤ-Number : Number ℤ
  ℤ-Number = record
    { Constraint = λ _ → ⊤
    ; fromNat = λ x → ⟦ x – 0 ⟧
    }

  ℤ-Negative : Negative ℤ
  ℤ-Negative = record
    { Constraint = λ _ → ⊤
    ; fromNeg = λ x → ⟦ 0 – x ⟧
    }

suc–suc-injective : ∀ a b → Path ℤ ⟦ suc a – suc b ⟧ ⟦ a – b ⟧
suc–suc-injective a b = equiv (suc a – suc b) (a – b) (sym (+-suc a b ))

⟦negate⟧ : ⟦ℤ⟧ → ⟦ℤ⟧
⟦negate⟧ (a – b) = b – a

negate : ℤ → ℤ
negate =
  ⟦negate⟧ // λ where
    (a – b) (c – d) p →
      ⟨ +-comm b c ⟩ ≫ sym p ≫ ⟨ +-comm a d ⟩

⟦plus⟧ : ⟦ℤ²⟧ → ⟦ℤ⟧
⟦plus⟧ ((a – b) , (c – d)) = (a + c) – (d + b)

plus : ℤ² → ℤ
plus =
  ⟦plus⟧ // λ where
    ((a – b) , (c – d)) ((e – f) , (g – h)) (p , q) →
        (a + c) + (h + f)
      ≡⟨ sym (ℕ.+-assoc a _ _) ⟩
        a + (c + (h + f))
      ≡⟨ cong (a +_) (ℕ.+-assoc c _ _) ⟩
        a + ((c + h) + f)
      ≡⟨ cong (λ z → a + (z + f)) q ⟩
        a + ((g + d) + f)
      ≡⟨ cong (a +_) ⟨ ℕ.+-comm (g + d) _ ⟩ ⟩
        a + (f + (g + d))
      ≡⟨ ℕ.+-assoc a _ _ ⟩
        (a + f) + (g + d)
      ≡⟨ cong (_+ (g + d)) p ⟩
        (e + b) + (g + d)
      ≡⟨ ℕ.+-cross e _ _ _ ⟩
        (e + g) + (b + d)
      ≡⟨ cong ((e + g) +_) ⟨ ℕ.+-comm b _ ⟩ ⟩
        (e + g) + (d + b)
      ∎

instance
  ⟦ℤ⟧-plus-syntax : plus-syntax-simple ⟦ℤ⟧ ⟦ℤ⟧ ⟦ℤ⟧
  ⟦ℤ⟧-plus-syntax = λ where ._+_ x y → ⟦plus⟧ (x , y)

  ⟦ℤ⟧-minus-syntax : minus-syntax-simple ⟦ℤ⟧ ⟦ℤ⟧ ⟦ℤ⟧
  ⟦ℤ⟧-minus-syntax = λ where ._-_ x y → ⟦plus⟧ (x , ⟦negate⟧ y)

  ℕ-⟦ℤ⟧-minus-syntax : minus-syntax-simple ℕ ℕ ⟦ℤ⟧
  ℕ-⟦ℤ⟧-minus-syntax = λ where ._-_ → _–_

  ℤ-plus-syntax : plus-syntax-simple ℤ ℤ ℤ
  ℤ-plus-syntax = λ where ._+_ → /.uncurry refl refl plus

  ℤ-minus-syntax : minus-syntax-simple ℤ ℤ ℤ
  ℤ-minus-syntax = λ where ._-_ x y → x + negate y

  ℕ-ℤ-minus-syntax : minus-syntax-simple ℕ ℕ ℤ
  ℕ-ℤ-minus-syntax = λ where ._-_ x y → ⟦ x – y ⟧
