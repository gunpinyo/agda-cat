{-# OPTIONS --without-K #-}

module Library where

open import Level
  using    ( Level )
  renaming ( zero to ℓ-zero
           ; suc  to ℓ-suc
           ; _⊔_  to ℓ-max )
  public

open import Function
  using    ()
  renaming ( id   to λ-id
           ; _∘_  to λ-comp
           ; flip to λ-flip )
  public

open import Relation.Binary.PropositionalEquality
  using    ( _≡_ )
  renaming ( refl  to ≡-refl
           ; sym   to ≡-sym
           ; trans to ≡-trans )
  public
