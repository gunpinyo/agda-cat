{-# OPTIONS --without-K #-}
open import Library

--------------------------------------------------------------------------------
-- Universes for a Category
--------------------------------------------------------------------------------

record CatLevel : Set where
  field
    Obj  : Level
    Hom  : Level

  Obj-Hom : Level
  Obj-Hom = ℓ-max Obj Hom

  Cat : Level
  Cat = ℓ-suc (ℓ-max Obj Hom)

--------------------------------------------------------------------------------
-- Definition of a Category
--------------------------------------------------------------------------------

module _ (ℓ : CatLevel) (let module ℓ = CatLevel ℓ) where
  record Category : Set ℓ.Cat where
    field
      Obj   : Set ℓ.Obj
      _⇒_   : Obj → Obj → Set ℓ.Hom
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

    op : Category
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

    record _≅_ (X Y : Obj) : Set ℓ.Cat where
      field
        f   : X ⇒ Y
        g   : Y ⇒ X
        g∘f : g ∘ f ≡ id X
        f∘g : f ∘ g ≡ id Y

    record _≾_ (X Y : Obj) : Set ℓ.Cat where
      field
        s   : X ⇒ Y
        r   : Y ⇒ X
        r∘s : r ∘ s ≡ id X

    module _ {X Y : Obj} (f : X ⇒ Y) where
      is-isomorphism  : Set ℓ.Hom
      is-isomorphism  = Σ[ g ∈ Y ⇒ X ] (g ∘ f ≡ id X) × (f ∘ g ≡ id Y)

      is-section      : Set ℓ.Hom
      is-section      = Σ[ g ∈ Y ⇒ X ] g ∘ f ≡ id X

      is-retraction   : Set ℓ.Hom
      is-retraction   = Σ[ g ∈ Y ⇒ X ] f ∘ g ≡ id Y

      is-monomorphism : Set ℓ.Obj-Hom
      is-monomorphism = ∀{Z}{g h : Z ⇒ X} → f ∘ g ≡ f ∘ h → g ≡ h

      is-epimorphism  : Set ℓ.Obj-Hom
      is-epimorphism  = ∀{Z}{g h : Y ⇒ Z} → g ∘ f ≡ h ∘ f → g ≡ h

      is-bimorphism   : Set ℓ.Obj-Hom
      is-bimorphism   = is-monomorphism × is-epimorphism

    module _ (X Y : Obj) where
      _iso⇒_  : Set ℓ.Hom
      _iso⇒_  = Σ (X ⇒ Y) is-isomorphism

      _mono⇒_ : Set ℓ.Obj-Hom
      _mono⇒_ = Σ (X ⇒ Y) is-monomorphism

      _epi⇒_  : Set ℓ.Obj-Hom
      _epi⇒_  = Σ (X ⇒ Y) is-epimorphism

--------------------------------------------------------------------------------
-- Category of Sets i.e. Types that has no non-trival equality
--------------------------------------------------------------------------------

SetCat : (ℓ : Level) → Category (record { Obj = ℓ-suc ℓ ; Hom = ℓ })
SetCat ℓ = record
  { Obj   = Object
  ; _⇒_   = λ (X Y : Object) → (X → Y)
  ; id    = λ (X : Object) → (λ x → x)
  ; _∘_   = λ {X Y Z : Object} (g : Y → Z) (f : X → Y) → (λ x → g (f x))
  ; idl   = ≡-refl
  ; idr   = ≡-refl
  ; assoc = ≡-refl
  } where Object = Set ℓ

SetCat₀ = SetCat ℓ-zero
