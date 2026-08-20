import Mathlib

namespace IUTSourceShape

universe u₀ u₁ u₂ u₃

def conjugate
    {A₀ : Type u₀} {A₁ : Type u₁}
    {C₀ : Type u₂} {C₁ : Type u₃}
    (k₀ : A₀ ≃ C₀) (k₁ : A₁ ≃ C₁) (h : A₀ ≃ A₁) : C₀ ≃ C₁ :=
  k₀.symm.trans (h.trans k₁)

@[simp] theorem conjugate_apply_kummer
    {A₀ : Type u₀} {A₁ : Type u₁}
    {C₀ : Type u₂} {C₁ : Type u₃}
    (k₀ : A₀ ≃ C₀) (k₁ : A₁ ≃ C₁) (h : A₀ ≃ A₁)
    (x : A₀) :
    conjugate k₀ k₁ h (k₀ x) = k₁ (h x) := by
  simp [conjugate]

def fullPolyIso (α : Type u₀) (β : Type u₁) : Set (α ≃ β) := Set.univ

@[simp] theorem mem_fullPolyIso
    {α : Type u₀} {β : Type u₁} (e : α ≃ β) :
    e ∈ fullPolyIso α β := by
  simp [fullPolyIso]

theorem conjugate_mem_full
    {A₀ : Type u₀} {A₁ : Type u₁}
    {C₀ : Type u₂} {C₁ : Type u₃}
    (k₀ : A₀ ≃ C₀) (k₁ : A₁ ≃ C₁) (h : A₀ ≃ A₁) :
    conjugate k₀ k₁ h ∈ fullPolyIso C₀ C₁ := by
  simp [fullPolyIso]

end IUTSourceShape
