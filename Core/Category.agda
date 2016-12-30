{-# OPTIONS --without-K #-}

module Core/Category where

open import Library

--------------------------------------------------------------------------------
-- Universe levels for Category
--------------------------------------------------------------------------------

record CatLevel : Set where
  constructor mk
  field
    Obj-ℓ : Level
    hom-ℓ : Level

  Self-ℓ : Level
  Self-ℓ = ℓ-suc (ℓ-max Obj-ℓ hom-ℓ)

--------------------------------------------------------------------------------
-- Category Definition
--------------------------------------------------------------------------------

record Category (Cat-ℓ : CatLevel) : Set (CatLevel.Self-ℓ Cat-ℓ) where
  constructor mk
  open CatLevel Cat-ℓ

  field
    Obj   : Set Obj-ℓ
    _⇒_   : Obj → Obj → Set hom-ℓ
    id    : (X : Obj) → X ⇒ X
    _∘_   : ∀{X Y Z} → Y ⇒ Z → X ⇒ Y → X ⇒ Z

  infix 4 _⇒_
  infix 6 _∘_

  field
    idl   : ∀{X Y}{f : X ⇒ Y} → (id Y) ∘ f ≡ f
    idr   : ∀{X Y}{f : X ⇒ Y} → f ∘ (id X) ≡ f
    assoc : ∀{W X Y Z}{f : W ⇒ X}{g : X ⇒ Y}{h : Y ⇒ Z}
              → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)

--------------------------------------------------------------------------------
-- Dual Category
--------------------------------------------------------------------------------

  op : Category Cat-ℓ
  op = record { Obj    = Obj
              ; _⇒_    = λ-flip _⇒_
              ; id     = id
              ; _∘_    = λ-flip _∘_
              ; idl    = idr
              ; idr    = idl
              ; assoc  = ≡-sym assoc }

--------------------------------------------------------------------------------
-- Isomorphism
--------------------------------------------------------------------------------

  record _≅_ (X Y : Obj) : Set Self-ℓ where
    field
      f   : X ⇒ Y
      g   : Y ⇒ X
      g∘f : g ∘ f ≡ id X
      f∘g : f ∘ g ≡ id Y
