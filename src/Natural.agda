module Natural where

open import Equality
open import Cubical.Data.Nat.Properties public
open import Data.Empty
open import Data.Nat as ℕ public hiding (_+_; _*_; _^_)
open import Data.Nat.Properties public hiding (+-assoc; +-suc)
open import Data.Unit
open import Function
open import Syntax

instance
  ℕ-plus-syntax : plus-syntax-simple ℕ ℕ ℕ
  ℕ-plus-syntax = record { _+_ = ℕ._+_ }

  ℕ-times-syntax : times-syntax-simple ℕ ℕ ℕ
  ℕ-times-syntax = record { _*_ = ℕ._*_ }

  ℕ-raise-syntax : raise-syntax-simple ℕ ℕ ℕ
  ℕ-raise-syntax = record { _^_ = ℕ._^_ }

+-cross : (a b c d : ℕ) → (a + b) + (c + d) ≡ (a + c) + (b + d)
+-cross a b c d =
    (a + b) + (c + d)
  ≡⟨ sym (+-assoc a _ _) ⟩
    a + (b + (c + d))
  ≡⟨ cong (a +_) (+-assoc b _ _) ⟩
    a + ((b + c) + d)
  ≡⟨ cong (a +_) (cong (_+ d) ⟨ +-comm b c ⟩) ⟩
    a + ((c + b) + d)
  ≡⟨ cong (a +_) (sym (+-assoc c _ _)) ⟩
    a + (c + (b + d))
  ≡⟨ +-assoc a _ _ ⟩
    (a + c) + (b + d)
  ∎

instance
  ℕ-Number : Number ℕ
  ℕ-Number = record { Constraint = λ _ → ⊤ ; fromNat = λ x → x }
