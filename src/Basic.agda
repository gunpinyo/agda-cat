{-# OPTIONS --without-K #-}
open import Library

--------------------------------------------------------------------------------
-- Universes for a Category
--------------------------------------------------------------------------------

record CatLevel : Set where
  open Library

  field
    Obj-ℓ  : Level
    Hom-ℓ  : Level

  Prop-ℓ : Level
  Prop-ℓ = ℓ-max Obj-ℓ Hom-ℓ

  Self-ℓ : Level
  Self-ℓ = ℓ-suc (ℓ-max Obj-ℓ Hom-ℓ)

--------------------------------------------------------------------------------
-- Definition of Category
--------------------------------------------------------------------------------

record Category (Cat-ℓ : CatLevel) : Set (CatLevel.Self-ℓ Cat-ℓ) where
  open CatLevel Cat-ℓ

  field
    Obj   : Set Obj-ℓ
    _⇒_   : Rel Obj Hom-ℓ
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
-- Properties of Spacial Morphisms
--------------------------------------------------------------------------------

  record _≅_ (X Y : Obj) : Set Self-ℓ where
    field
      f   : X ⇒ Y
      g   : Y ⇒ X
      g∘f : g ∘ f ≡ id X
      f∘g : f ∘ g ≡ id Y

  record isIsomorphism {X Y : Obj} (f : X ⇒ Y) : Set Self-ℓ where
    field
      X≅Y  : X ≅ Y
      cond : _≅_.f X≅Y ≡ f

  record isSection {X Y : Obj} (s : X ⇒ Y) : Set Self-ℓ where
    field
      r   : Y ⇒ X
      r∘s : r ∘ s ≡ id X

  record isRetraction {X Y : Obj} (r : Y ⇒ X) : Set Self-ℓ where
    field
      s   : X ⇒ Y
      r∘s : r ∘ s ≡ id X

  isMonic : {X Y : Obj} → X ⇒ Y → Set Prop-ℓ
  isMonic {Y} {Z} f = ∀{X}{g h : X ⇒ Y} → f ∘ g ≡ f ∘ h → g ≡ h

  isEpic : {X Y : Obj} → X ⇒ Y → Set Prop-ℓ
  isEpic {X} {Y} f = ∀{Z}{g h : Y ⇒ Z} → g ∘ f ≡ h ∘ f → g ≡ h

  record isBimorphism {X Y : Obj} (f : X ⇒ Y) : Set Prop-ℓ where
    field
      monic : isMonic f
      epic  : isEpic f

--------------------------------------------------------------------------------
-- Definition of Functor
--------------------------------------------------------------------------------

record Functor {C-ℓ D-ℓ : CatLevel} (C : Category C-ℓ) (D : Category D-ℓ)
    : Set (ℓ-max (CatLevel.Self-ℓ C-ℓ) (CatLevel.Self-ℓ D-ℓ)) where
  open module C = Category C using () renaming (_⇒_ to _⇒ᶜ_ ; _∘_ to _∘ᶜ_)
  open module D = Category D using () renaming (_⇒_ to _⇒ᵈ_ ; _∘_ to _∘ᵈ_)

  field
    map  : C.Obj → D.Obj
    fmap : ∀{X Y} → X ⇒ᶜ Y → (map X) ⇒ᵈ (map Y)

  field
    id   : ∀{X} → fmap (C.id X) ≡ D.id (map X)
    comp : ∀{X Y Z}{f : X ⇒ᶜ Y}{g : Y ⇒ᶜ Z}
             → fmap (g ∘ᶜ f) ≡ (fmap g) ∘ᵈ (fmap f)

--------------------------------------------------------------------------------
-- Definition of Natural Transformation
--------------------------------------------------------------------------------

record NaturalTrans {C-ℓ D-ℓ : CatLevel}
    {C : Category C-ℓ} {D : Category D-ℓ} (F : Functor C D)  (G : Functor C D)
    : Set (ℓ-max (CatLevel.Self-ℓ C-ℓ) (CatLevel.Self-ℓ D-ℓ)) where
  open module C = Category C using ()    renaming (_⇒_ to _⇒ᶜ_)
  open module D = Category D using (_∘_) renaming (_⇒_ to _⇒ᵈ_)
  module F = Functor F
  module G = Functor G

  field
    map  : (X : C.Obj) → (F.map X) ⇒ᵈ (G.map X)
    comm : ∀{X Y}{f : X ⇒ᶜ Y} → (G.fmap f) ∘ (map X) ≡ (map Y) ∘ (F.fmap f)

--------------------------------------------------------------------------------
-- Definition of Natrual Isomorphism
--------------------------------------------------------------------------------

-- record NaturalIso
