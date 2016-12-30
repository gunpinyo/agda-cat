module Excercises where

open import Library
open import Core/Category

SmallType : Category (mk (ℓ-suc ℓ-zero) ℓ-zero)
SmallType = record
  { Obj   = Set
  ; _⇒_   = λ (X Y : Set) → (X → Y)
  ; id    = λ (X : Set) → (λ x → x)
  ; _∘_   = λ {X Y Z : Set} (g : Y → Z) (f : X → Y) → (λ x → g (f x))
  ; idl   = ≡-refl
  ; idr   = ≡-refl
  ; assoc = ≡-refl
  }
