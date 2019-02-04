{-# OPTIONS --cubical #-}

module Integer.Univalence where

open import Cubical.Foundations.NTypes
open import Data.Empty
open import Data.Product as Σ
open import Data.Product.Relation.Pointwise.NonDependent
open import Data.Unit
open import Equality
open import Function
open import Integer.Difference as D
open import Integer.Signed as S
open import Natural as ℕ
open import Quotient as /
open import Syntax
open import Relation.Nullary

zero≢suc : ∀ {m} → ¬ (zero ≡ suc m)
zero≢suc p = case ⟪ p ⟫ of λ ()

⟦D→S⟧ : D.⟦ℤ⟧ → S.⟦ℤ⟧
⟦D→S⟧ (a – zero) = +1* a
⟦D→S⟧ (zero – b) = -1* b
⟦D→S⟧ (suc a – suc b) = ⟦D→S⟧ (a – b)

D→S : D.ℤ → S.ℤ
D→S = ⟦D→S⟧ // line
  where
    line : ∀ x y → x D.≈ y → ⟦D→S⟧ x S.≈ ⟦D→S⟧ y
    line (zero – zero) (zero – zero) p = refl
    line (zero – zero) (zero – suc d) p = refl , p
    line (zero – zero) (suc c – zero) p = compPath p (cong suc ⟨ +-identityʳ c ⟩)
    line (zero – b) (suc c – suc d) p = line (zero – b) (c – d) ⟨ suc-injective ⟪ p ⟫ ⟩
    line (suc a – suc b) (zero – d) p = line (a – b) (zero – d) ⟨ suc-injective ⟪ p ⟫ ⟩
    line (zero – suc b) (zero – zero) p = sym p , refl
    line (zero – suc b) (zero – suc d) p = sym p
    line (zero – suc b) (suc c – zero) p = case ⟪ p ⟫ of λ ()
    line (suc a – zero) (zero – d) p = case ⟪ p ⟫ of λ ()
    line (suc a – zero) (suc c – zero) p =
        suc a
      ≡⟨ cong suc (sym ⟨ +-identityʳ a ⟩) ⟩
        suc (a + 0)
      ≡⟨ p ⟩
        suc (c + 0)
      ≡⟨ cong suc ⟨ +-identityʳ c ⟩ ⟩
        suc c
      ∎
    line (suc a – b) (suc c – suc d) p =
      line (suc a – b) (c – d)
        ⟨ suc-injective ⟪ compPath (cong suc (sym (+-suc a d))) p ⟫ ⟩
    line (suc a – suc b) (suc c – d) p =
      line (a – b) (suc c – d)
        ⟨ suc-injective ⟪ compPath p (cong suc (+-suc c b)) ⟫ ⟩

⟦S→D⟧ : S.⟦ℤ⟧ → D.⟦ℤ⟧
⟦S→D⟧ (+1* a) = a – zero
⟦S→D⟧ (-1* a) = zero – a

⟦D→S→D⟧ : ∀ x → ⟦S→D⟧ (⟦D→S⟧ x) D.≈ x
⟦D→S→D⟧ (zero – zero) = refl
⟦D→S→D⟧ (zero – suc b) = refl
⟦D→S→D⟧ (suc a – zero) = refl
⟦D→S→D⟧ (suc a – suc b) =
  let m , n = ⟦S→D⟧ (⟦D→S⟧ (a – b)) in
      m + suc b
    ≡⟨ +-suc m b ⟩
      suc (m + b)
    ≡⟨ cong suc (⟦D→S→D⟧ (a – b)) ⟩
      suc (a + n)
    ∎

⟦S→D→S⟧ : ∀ x → ⟦D→S⟧ (⟦S→D⟧ x) S.≈ x
⟦S→D→S⟧ (+1* x) = refl
⟦S→D→S⟧ (-1* zero) = refl , refl
⟦S→D→S⟧ (-1* suc x) = refl

cong-⟦S→D⟧ : ∀ x y → x S.≈ y → ⟦S→D⟧ x D.≈ ⟦S→D⟧ y
cong-⟦S→D⟧ (+1* x) (+1* y) = cong (_+ zero)
cong-⟦S→D⟧ (-1* x) (-1* y) = sym
cong-⟦S→D⟧ (+1* x) (-1* y) = Σ.uncurry (cong₂ _+_)
cong-⟦S→D⟧ (-1* x) (+1* y) (p , q) = compPath (sym (cong₂ _+_ p q)) ⟨ +-comm x y ⟩

cong-⟦D→S⟧ : ∀ x y → x D.≈ y → ⟦D→S⟧ x S.≈ ⟦D→S⟧ y
cong-⟦D→S⟧ (zero – zero) (zero – zero) p = refl
cong-⟦D→S⟧ (zero – zero) (zero – suc d) p = refl , p
cong-⟦D→S⟧ (zero – zero) (suc c – zero) p = compPath p (cong suc ⟨ +-identityʳ c ⟩)
cong-⟦D→S⟧ (zero – b) (suc c – suc d) p = cong-⟦D→S⟧ (zero – b) (c – d) ⟨ suc-injective ⟪ p ⟫ ⟩
cong-⟦D→S⟧ (suc a – suc b) (zero – d) p = cong-⟦D→S⟧ (a – b) (zero – d) ⟨ suc-injective ⟪ p ⟫ ⟩
cong-⟦D→S⟧ (zero – suc b) (zero – zero) p = sym p , refl
cong-⟦D→S⟧ (zero – suc b) (zero – suc d) p = sym p
cong-⟦D→S⟧ (zero – suc b) (suc c – zero) p = case ⟪ p ⟫ of λ ()
cong-⟦D→S⟧ (suc a – zero) (zero – d) p = case ⟪ p ⟫ of λ ()
cong-⟦D→S⟧ (suc a – zero) (suc c – zero) p =
    suc a
  ≡⟨ cong suc (sym ⟨ +-identityʳ a ⟩) ⟩
    suc (a + 0)
  ≡⟨ p ⟩
    suc (c + 0)
  ≡⟨ cong suc ⟨ +-identityʳ c ⟩ ⟩
    suc c
  ∎
cong-⟦D→S⟧ (suc a – b) (suc c – suc d) p =
  cong-⟦D→S⟧ (suc a – b) (c – d)
    ⟨ suc-injective ⟪ compPath (cong suc (sym (+-suc a d))) p ⟫ ⟩
cong-⟦D→S⟧ (suc a – suc b) (suc c – d) p =
  cong-⟦D→S⟧ (a – b) (suc c – d)
    ⟨ suc-injective ⟪ compPath p (cong suc (+-suc c b)) ⟫ ⟩

Signed≡Difference : S.ℤ ≡ D.ℤ
Signed≡Difference = ua (isoToEquiv ⟦S→D⟧ ⟦D→S⟧ cong-⟦S→D⟧ cong-⟦D→S⟧ ⟦S→D→S⟧ ⟦D→S→D⟧)
