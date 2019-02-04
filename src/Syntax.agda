module Syntax where

open import Agda.Builtin.FromNat public
open import Agda.Builtin.FromNeg public

record plus-syntax (A : Set) (B : A → Set) (C : ∀ x → B x → Set) : Set where
  infixl 6 _+_
  field _+_ : ∀ x (y : B x) → C x y

plus-syntax-simple = λ A B C → plus-syntax A (λ _ → B) (λ _ _ → C)

open plus-syntax {{…}} public

record minus-syntax (A : Set) (B : A → Set) (C : ∀ x → B x → Set) : Set where
  infixl 6 _-_
  field _-_ : ∀ x (y : B x) → C x y

minus-syntax-simple = λ A B C → minus-syntax A (λ _ → B) (λ _ _ → C)

open minus-syntax {{…}} public

record times-syntax (A : Set) (B : A → Set) (C : ∀ x → B x → Set) : Set where
  infixl 7 _*_
  field _*_ : ∀ x (y : B x) → C x y

times-syntax-simple = λ A B C → times-syntax A (λ _ → B) (λ _ _ → C)

open times-syntax {{…}} public

record raise-syntax (A : Set) (B : A → Set) (C : ∀ x → B x → Set) : Set where
  infixl 8 _^_
  field _^_ : ∀ x (y : B x) → C x y

raise-syntax-simple = λ A B C → raise-syntax A (λ _ → B) (λ _ _ → C)

open raise-syntax {{…}} public
