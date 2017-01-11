{-# OPTIONS --without-K #-}
open import Library
open import Basic

--------------------------------------------------------------------------------
-- Universes for a Functor
--------------------------------------------------------------------------------

record FntrLevel : Set where
  field
    C : CatLevel
    D : CatLevel

  module C = CatLevel C
  module D = CatLevel D

  Fntr : Level
  Fntr = ℓ-max C.Cat D.Cat

--------------------------------------------------------------------------------
-- Definition of a Functor
--------------------------------------------------------------------------------

module _ {ℓ : FntrLevel}    (let module ℓ = FntrLevel ℓ)
         (C : Category ℓ.C) (let module C = Category C)
           (open C using () renaming (_⇒_ to _⇒ᶜ_ ; _∘_ to _∘ᶜ_))
         (D : Category ℓ.D) (let module D = Category D)
           (open D using () renaming (_⇒_ to _⇒ᵈ_ ; _∘_ to _∘ᵈ_)) where

  record Functor : Set ℓ.Fntr where
    field
      map  : C.Obj → D.Obj
      fmap : ∀{X Y} → X ⇒ᶜ Y → (map X) ⇒ᵈ (map Y)

    field
      id   : ∀{X} → fmap (C.id X) ≡ D.id (map X)
      comp : ∀{X Y Z}{f : X ⇒ᶜ Y}{g : Y ⇒ᶜ Z}
               → fmap (g ∘ᶜ f) ≡ (fmap g) ∘ᵈ (fmap f)

--------------------------------------------------------------------------------
-- Definition of a Natural Transformation and a Natural Isomorphism
--------------------------------------------------------------------------------

module _ {ℓ : FntrLevel}     (let module ℓ = FntrLevel ℓ)
         {C : Category ℓ.C}  (let module C = Category C)
           (open C using () renaming (_⇒_ to _⇒ᶜ_ ; _∘_ to _∘ᶜ_))
         {D : Category ℓ.D}  (let module D = Category D)
           (open D using () renaming (_⇒_ to _⇒ᵈ_ ; _∘_ to _∘ᵈ_))
         (F G : Functor C D) (let module F = Functor F)
                                 (let module G = Functor G) where

  record NaturalTrans : Set ℓ.Fntr where
    field
      map    : (X : C.Obj) → (F.map X) ⇒ᵈ (G.map X)
      nat-sq : {X Y : C.Obj}{f : X ⇒ᶜ Y} →
                 (G.fmap f) ∘ᵈ (map X) ≡ (map Y) ∘ᵈ (F.fmap f)

    is-natrual-isomorphism : Set (ℓ-max ℓ.C.Obj ℓ.D.Hom)
    is-natrual-isomorphism = ∀(X : C.Obj) → D.is-isomorphism (map X)

  NaturalIso : Set ℓ.Fntr
  NaturalIso = Σ NaturalTrans NaturalTrans.is-natrual-isomorphism

--------------------------------------------------------------------------------
-- Category of Functors
--------------------------------------------------------------------------------

module _ {ℓ : FntrLevel}     (let module ℓ = FntrLevel ℓ)
         (C : Category ℓ.C) (let module C = Category C)
           (open C using () renaming (_⇒_ to _⇒ᶜ_ ; _∘_ to _∘ᶜ_))
         (D : Category ℓ.D) (let module D = Category D)
           (open D using () renaming (_⇒_ to _⇒ᵈ_ ; _∘_ to _∘ᵈ_)) where

  FntrCat : Category (record { Obj = ℓ.Fntr ; Hom = ℓ.Fntr })
  FntrCat = record { Obj   = Functor C D
                   ; _⇒_   = NaturalTrans
                   ; id    = natural-trans-id
                   ; _∘_   = vertical-comp
                   ; idl   = {!!}
                   ; idr   = {!!}
                   ; assoc = {!!} }
    where
      natural-trans-id : (F : Functor C D) → NaturalTrans F F
      natural-trans-id F = record
        { map    = λ (X : C.Obj) → D.id (F.map X)
        ; nat-sq = λ {X Y : C.Obj} {f : X ⇒ᶜ Y} →               ≡-proof
            (F.fmap f) ∘ᵈ D.id (F.map X)                        ≡⟨ D.idr       ⟩
            F.fmap f                                            ≡⟨ ≡-sym D.idl ⟩
            D.id (F.map Y) ∘ᵈ (F.fmap f)                        ≡-qed
        } where module F = Functor F

      vertical-comp : {F G H : Functor C D}
                        → NaturalTrans G H → NaturalTrans F G → NaturalTrans F H
      vertical-comp {F} {G} {H} β α = record
        { map    = λ (X : C.Obj) → (β.map X) ∘ᵈ (α.map X)
        ; nat-sq = λ {X Y : C.Obj} {f : X ⇒ᶜ Y} →           ≡-proof
            H.fmap f ∘ᵈ (β.map X ∘ᵈ α.map X)          ≡⟨ ≡-sym D.assoc ⟩
            (H.fmap f ∘ᵈ β.map X) ∘ᵈ α.map X          ≡⟨ {!!} ⟩
            (β.map Y ∘ᵈ G.fmap f) ∘ᵈ α.map X          ≡⟨ D.assoc ⟩
            β.map Y ∘ᵈ (G.fmap f ∘ᵈ α.map X)          ≡⟨ {!!} ⟩
            β.map Y ∘ᵈ (α.map Y ∘ᵈ F.fmap f)          ≡⟨ ≡-sym D.assoc ⟩
            (β.map Y ∘ᵈ α.map Y) ∘ᵈ F.fmap f            ≡-qed
        } where module F = Functor F
                module G = Functor G
                module H = Functor H
                module α = NaturalTrans α
                module β = NaturalTrans β

--------------------------------------------------------------------------------
-- Definition of Presheaf
--------------------------------------------------------------------------------

-- module _ {C : CatLevel} (open CatLevel C)
--          (C : Category C) (let module C = Category C) where
--   Presheaf : Category (record { Obj = ℓ-suc Obj ; Hom = ℓ-suc Hom })
--   Presheaf C = record { Obj = Functor C.op (Type Hom)
--                       ; _⇒_ = NaturalTrans
--                       ; id  = NaturalTrans-id
--                       ; __}
