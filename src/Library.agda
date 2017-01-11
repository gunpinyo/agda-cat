{-# OPTIONS --without-K #-}

module Library where

open import Data.Product
  using    ( Σ ; Σ-syntax ; _×_ )
  public

open import Function
  using    ()
  renaming ( id   to λ-id
           ; _∘_  to λ-comp
           ; flip to λ-flip )
  public

open import Level
  using    ( Level )
  renaming ( zero to ℓ-zero
           ; suc  to ℓ-suc
           ; _⊔_  to ℓ-max )
  public

open import Relation.Binary.Core
  using    ( Rel )
  public

open import Relation.Unary
  using    ( Pred )
  public

open import Relation.Binary.PropositionalEquality
  using    ( _≡_ ; module ≡-Reasoning )
  renaming ( refl  to ≡-refl
           ; sym   to ≡-sym
           ; trans to ≡-trans)
  public

open ≡-Reasoning
  using    ( _≡⟨_⟩_ )
  renaming ( begin_ to ≡-proof_
           ; _∎     to _≡-qed )
  public
