{-# OPTIONS --without-K #-}

module Core/Functor where

open import Library
open import Core/Category

--------------------------------------------------------------------------------
-- Functor Definition
--------------------------------------------------------------------------------

record Functor {C-ℓ D-ℓ : CatLevel} (C : Category C-ℓ) (D : Category D-ℓ)
    : Set (ℓ-max (CatLevel.Self-ℓ C-ℓ) (CatLevel.Self-ℓ D-ℓ)) where
  constructor mk
  open module C = Category C using () renaming (_⇒_ to _⇒ᶜ_ ; _∘_ to _∘ᶜ_)
  open module D = Category D using () renaming (_⇒_ to _⇒ᵈ_ ; _∘_ to _∘ᵈ_)

  field
    map  : C.Obj → D.Obj
    fmap : ∀{X Y} → X ⇒ᶜ Y → (map X) ⇒ᵈ (map Y)

  field
    id   : ∀{X} → fmap (C.id X) ≡ D.id (map X)
    comp : ∀{X Y Z}{f : X ⇒ᶜ Y}{g : Y ⇒ᶜ Z}
             → fmap (g ∘ᶜ f) ≡ (fmap g) ∘ᵈ (fmap f)
