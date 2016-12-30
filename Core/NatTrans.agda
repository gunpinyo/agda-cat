{-# OPTIONS --without-K #-}

module Core/NatTrans where

open import Library
open import Core/Category
open import Core/Functor

--------------------------------------------------------------------------------
-- Natural Transformation Definition
--------------------------------------------------------------------------------

record NatTrans {C-ℓ D-ℓ : CatLevel} {C : Category C-ℓ} {D : Category D-ℓ}
                                     (F : Functor C D)  (G : Functor C D)
    : Set (ℓ-max (CatLevel.Self-ℓ C-ℓ) (CatLevel.Self-ℓ D-ℓ)) where
  constructor mk
  open module C = Category C using ()    renaming (_⇒_ to _⇒ᶜ_)
  open module D = Category D using (_∘_) renaming (_⇒_ to _⇒ᵈ_)
  module F = Functor F
  module G = Functor G

  field
    map  : (X : C.Obj) → (F.map X) ⇒ᵈ (G.map X)
    comm : ∀{X Y}{f : X ⇒ᶜ Y} → (G.fmap f) ∘ (map X) ≡ (map Y) ∘ (F.fmap f)
