{-# OPTIONS --without-K --safe #-}

module Relation.Binary.PartialEquivalence where

open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (sym to ≡-sym; trans to ≡-trans; refl to ≡-refl)
open import Relation.Nullary using (¬_)

open import Level

private
  variable
    a b c ℓ : Level
    A : Set a

------------------------------------------------------------------------
-- Partial equivalence relations
------------------------------------------------------------------------

record IsPartialEquivalence {A : Set a} (_≈_ : Rel A ℓ) : Set (a ⊔ ℓ) where
  field
    sym : Symmetric _≈_
    trans : Transitive _≈_

------------------------------------------------------------------------
-- Partial setoids

-- We parameterize over a carrier set rather than
-- including the carrier over a field to make
-- subsets and membership simpler
------------------------------------------------------------------------

record PartialSetoid c ℓ (A : Set c) : Set (suc (c ⊔ ℓ)) where
  infix 4 _≈_
  field
    _≈_ : Rel A ℓ
    isPartialEquivalence : IsPartialEquivalence _≈_

  open IsPartialEquivalence isPartialEquivalence public

  _≉_ : Rel A _
  x ≉ y = ¬ (x ≈ y)

-- Membership in a partial setoid is the same
-- as having a proof of refl
_∈_ : ∀ {A : Set c} → A → PartialSetoid c ℓ A → Set _
x ∈ S = x ≈ x
  where open PartialSetoid S

_∉_ : ∀ {A : Set c} → A → PartialSetoid c ℓ A → Set _
x ∉ S = x ≉ x
  where open PartialSetoid S

_⊆_ : ∀ {A : Set c} → Rel (PartialSetoid c ℓ A) _
S ⊆ T = ∀ {x} → x ∈ S → x ∈ T

-- Two sets are equivalent when they are both subsets of one another
record _⇔_ {c ℓ} {A : Set c} (S : PartialSetoid c ℓ A) (T : PartialSetoid c ℓ A) : Set (c ⊔ ℓ) where
  field
    subsetˡ : S ⊆ T
    subsetʳ : T ⊆ S

-- Polymorphic bottom type for reasons
data ⊥ {ℓ} : Set ℓ where

⊥-elim : ∀ {w} {Whatever : Set w} → ⊥ {w} → Whatever
⊥-elim ()

∅ : ∀ {c ℓ} {A : Set c} → PartialSetoid c ℓ A
∅ = record {
  _≈_ = λ x y → ⊥
  ; isPartialEquivalence = record
    { sym = λ x → x ; trans = λ x _ → x }
  }

-- Any setoid is alo a partial setoid
partial-setoid : ∀ (S : Setoid c ℓ) → PartialSetoid c ℓ (Setoid.Carrier S)
partial-setoid S = record
  { _≈_ = _≈_
  ; isPartialEquivalence = record
    { sym = sym
    ; trans = trans }
  }
  where open Setoid S