module Integer.Difference.Properties where

open import Data.Product as Σ
open import Data.Product.Relation.Pointwise.NonDependent
open import Data.Unit
open import Equality
open import Integer.Difference
open import Natural as ℕ using (ℕ; zero; suc)
open import Quotient as /
open import Relation.Binary
open import Syntax

open Equality.FunctionProperties

+-comm : Commutative {A = ℤ} _+_
+-comm =
  ⟦⟧-≗₂ uip _ _ λ where
    (a – b) (c – d) →
      cong ⟦_⟧ (cong₂ _–_ (⟨ ℕ.+-comm a c ⟩) (⟨ ℕ.+-comm d b ⟩))

+-identityˡ : LeftIdentity {A = ℤ} 0 _+_
+-identityˡ =
  ⟦⟧-≗ uip _ _ λ where
    (a – b) →
      cong (λ z → ⟦ a – z ⟧) ⟨ ℕ.+-identityʳ b ⟩

+-identityʳ : RightIdentity {A = ℤ} 0 _+_
+-identityʳ =
  ⟦⟧-≗ uip _ _ λ where
    (a – b) →
      cong (λ z → ⟦ z – b ⟧) ⟨ ℕ.+-identityʳ a ⟩

+-assoc : Associative {A = ℤ} _+_
+-assoc =
  ⟦⟧-≗₃ uip _ _
    λ where
      (a – b) (c – d) (e – f) →
        cong ⟦_⟧ (cong₂ _–_ (sym (ℕ.+-assoc a _ _)) (ℕ.+-assoc f _ _))
