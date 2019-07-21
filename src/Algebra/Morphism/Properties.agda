{-# OPTIONS --without-K --safe #-}
module Algebra.Morphism.Properties where

open import Algebra
open import Algebra.Morphism

open import Function.Equality using (Π; _⟶_; _⟨$⟩_)
open import Function.Injection

open import Relation.Binary
open import Relation.Binary.PartialEquivalence

open import Level

module Kernel {c₁ ℓ₁ c₂ ℓ₂}
         {From : Group c₁ ℓ₁}
         {To : Group c₂ ℓ₂}
         (ϕ : (Group.setoid From) ⟶ (Group.setoid To))
         where
  private
    module F = Group From
    module T = Group To
  open Definitions F.Carrier T.Carrier T._≈_
  open F using (_⁻¹) renaming
    (_≈_ to _≈₁_
    ; ε to ε₁
    ; sym to ≈₁-sym
    ; trans to ≈₁-trans
    ; inverseʳ to inverseʳ₁
    ; _∙_ to _∙₁_)
  open T using () renaming
    (_≈_ to _≈₂_
    ; ε to ε₂
    ; sym to ≈₂-sym
    ; trans to ≈₂-trans
    ; refl to ≈₂-refl
    ; inverseʳ to inverseʳ₂
    ; _∙_ to _∙₂_
    ; ∙-cong to ∙₂-cong
    ; ⁻¹-cong to ⁻¹₂-cong
    ; _⁻¹ to _⁻¹̇)

  -- Two elements are in the kernel if and only if they both map to identity
  data _≈_ : Rel F.Carrier (c₁ ⊔ ℓ₁ ⊔ c₂ ⊔ ℓ₂) where
    g₁≈g₂ : ∀ {g₁ g₂} → ϕ ⟨$⟩ g₁ ≈₂ ε₂ → ϕ ⟨$⟩ g₂ ≈₂ ε₂ → g₁ ≈ g₂

  -- Helper for constructing equality proofs
  g≈ε : ∀ {g} → ϕ ⟨$⟩ g ≈₂ ε₂ → g ≈ g
  g≈ε ϕ⟨g⟩≈ε = g₁≈g₂ ϕ⟨g⟩≈ε ϕ⟨g⟩≈ε

  -- Some properties of kernel membership
  ≈-sym : Symmetric _≈_
  ≈-sym (g₁≈g₂ g₁≈ε g₂≈ε) = g₁≈g₂ g₂≈ε g₁≈ε

  ≈-trans : Transitive _≈_
  ≈-trans (g₁≈g₂ g₁≈ε _) (g₁≈g₂ _ g₂≈ε) = g₁≈g₂ g₁≈ε g₂≈ε

  -- The kernel of a homomorphism ϕ forms a partial setoid over the domain of ϕ
  kernel : PartialSetoid c₁ (c₁ ⊔ ℓ₁ ⊔ c₂ ⊔ ℓ₂) (F.Carrier)
  kernel = record
    { _≈_ = _≈_
    ; isPartialEquivalence = record
      { sym = ≈-sym
      ; trans = ≈-trans }
    }

  -- If the kernel is trivial, then the homomorphism is injective
  inj-kernelˡ : (IsGroupMorphism From To (_⟨$⟩_ ϕ)) → (∀ {g} → g ∈ kernel → g ≈₁ ε₁) → Injective ϕ
  inj-kernelˡ ϕ-homo kernel-sing {g₁} {g₂} ϕ⟨g₁⟩≈₂ϕ⟨g₂⟩ =
    ∙-cancelʳ g₁ g₂ (≈₁-trans (kernel-sing (g≈ε ϕ⟨g₁∙g₂⁻¹⟩≈ε)) (≈₁-sym (inverseʳ₁ g₂)))
    where open IsGroupMorphism ϕ-homo
          open import Algebra.Properties.Group From

          ϕ⟨g₁∙g₂⁻¹⟩≈ε : ϕ ⟨$⟩ (g₁ ∙₁ g₂ ⁻¹) ≈₂ ε₂
          ϕ⟨g₁∙g₂⁻¹⟩≈ε = begin
            ϕ ⟨$⟩ (g₁ ∙₁ g₂ ⁻¹) ≈⟨ ∙-homo g₁ (g₂ ⁻¹) ⟩
            (ϕ ⟨$⟩ g₁) ∙₂ (ϕ ⟨$⟩ g₂ ⁻¹) ≈⟨ ∙₂-cong ≈₂-refl (⁻¹-homo g₂) ⟩
            (ϕ ⟨$⟩ g₁) ∙₂ (ϕ ⟨$⟩ g₂) ⁻¹̇ ≈⟨ ∙₂-cong ≈₂-refl (⁻¹₂-cong (≈₂-sym ϕ⟨g₁⟩≈₂ϕ⟨g₂⟩)) ⟩
            (ϕ ⟨$⟩ g₁) ∙₂ (ϕ ⟨$⟩ g₁) ⁻¹̇ ≈⟨ inverseʳ₂ (ϕ ⟨$⟩ g₁) ⟩
            ε₂ ∎
            where open import Relation.Binary.Reasoning.Setoid (Group.setoid To)

  -- If the homomorphism is injective, then the kernel is trivial
  inj-kernelʳ : (IsGroupMorphism From To (_⟨$⟩_ ϕ)) → Injective ϕ → (∀ {g} → g ≈₁ ε₁ → g ∈ kernel)
  inj-kernelʳ ϕ-homo ϕ-inj g≈₁ε₁ = g≈ε (≈₂-trans (ϕ-cong g≈₁ε₁) ε-homo)
    where open IsGroupMorphism ϕ-homo
          open Π ϕ renaming (cong to ϕ-cong)