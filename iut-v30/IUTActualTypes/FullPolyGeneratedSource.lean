/-
Copyright (c) 2026 ChatGPT. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ChatGPT
-/
import IUTActualTypes.GeneratedSource

/-!
# Full-poly source adapter into the actual public container types

The source-side categories remain abstract because the public IUT repository does not
define Hodge theaters or Frobenioids.  All output, hull, and volume data, however, use
the actual public Corollary 3.12 types.

Two former assumptions are absent:

* the commuting coric representative is the Kummer conjugate;
* ordinary-branch membership is definitional in the generated choice type.
-/

namespace IUTActualTypes

open Iut NumberField

universe u v w u₀ u₁ u₂ u₃ u₄

/-- Kummer conjugation of a chosen horizontal equivalence. -/
def conjugateEquiv
    {A₀ : Type u₀} {A₁ : Type u₁}
    {C₀ : Type u₂} {C₁ : Type u₃}
    (k₀ : A₀ ≃ C₀) (k₁ : A₁ ≃ C₁) (h : A₀ ≃ A₁) : C₀ ≃ C₁ :=
  k₀.symm.trans (h.trans k₁)

@[simp]
theorem conjugateEquiv_apply_kummer
    {A₀ : Type u₀} {A₁ : Type u₁}
    {C₀ : Type u₂} {C₁ : Type u₃}
    (k₀ : A₀ ≃ C₀) (k₁ : A₁ ≃ C₁) (h : A₀ ≃ A₁) (x : A₀) :
    conjugateEquiv k₀ k₁ h (k₀ x) = k₁ (h x) := by
  simp [conjugateEquiv]

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}

/-- A full-poly source specification whose realized outputs live in the actual public
large-volume container. -/
structure FullPolyGeneratedSource
    (D : InitialThetaData AG TG)
    (Q : QPilotData D) : Type
      (max (u + 1) (v + 1) (w + 1) (u₀ + 1) (u₁ + 1)
        (u₂ + 1) (u₃ + 1) (u₄ + 1)) where
  container : LargeVolumeContainerData.{0, u, v} ℕ
    (Place ↥D.prime.torsionField)
  proc_standard :
    container.proc = Procession.standard ((D.ℓ - 1) / 2)
  toRational_finite : ∀ x : FinitePlace ↥D.prime.torsionField,
    (container.toRational (Place.finite x)).residueChar = residueChar x
  toRational_infinite : ∀ x : InfinitePlace ↥D.prime.torsionField,
    container.toRational (Place.infinite x) = RationalPlace.infinite
  vol : LogVolumeData container
  hull : ContainerHullSystem container

  A₀ : Type u₀
  A₁ : Type u₁
  C₀ : Type u₂
  C₁ : Type u₃
  kummer₀ : A₀ ≃ C₀
  kummer₁ : A₁ ≃ C₁
  horizontal : A₀ ≃ A₁
  thetaPilotObject : A₀
  qPilotObject : A₁
  horizontalPilot : horizontal thetaPilotObject = qPilotObject

  ExtraChoice : Type u₄
  extraOutput : ExtraChoice → C₁
  realize : C₁ → ∀ i, container.AdmissibleRegion i

  /-- A common finite support for every ordinary and extra output. -/
  support : ∀ i, Finset RationalPlace
  realize_eq_integral_outside :
    ∀ (x : C₁) i vQ, vQ ∉ support i →
      (realize x i).region vQ = (container.packet i vQ).integralRegion
  realize_le_logShell :
    ∀ (x : C₁) i, realize x i ≤ container.logShellAdmissible i
  union_hullAdmissible :
    ∀ i,
      hull.IsAdmissible
        (GeneratedOutputData.unionRegion
          ({ Output := Sum (C₀ ≃ C₁) ExtraChoice
             outputNonempty := ⟨Sum.inl (conjugateEquiv kummer₀ kummer₁ horizontal)⟩
             realize := fun c => match c with
               | .inl p => realize (p (kummer₀ thetaPilotObject))
               | .inr e => realize (extraOutput e)
             support := support
             realize_eq_integral_outside := by
               intro c i vQ hv
               cases c with
               | inl p => exact realize_eq_integral_outside _ i vQ hv
               | inr e => exact realize_eq_integral_outside _ i vQ hv
             realize_le_logShell := by
               intro c i
               cases c with
               | inl p => exact realize_le_logShell _ i
               | inr e => exact realize_le_logShell _ i } :
            GeneratedOutputData container) i)

  qVolume :
    vol.processionVol (realize (kummer₁ qPilotObject)) = Q.lhs
  processionVol_mono :
    ∀ {R S : ∀ i, container.AdmissibleRegion i},
      (∀ i, R i ≤ S i) →
        vol.processionVol R ≤ vol.processionVol S

namespace FullPolyGeneratedSource

variable {D : InitialThetaData AG TG} {Q : QPilotData D}

inductive Choice
    (S : FullPolyGeneratedSource.{u, v, w, u₀, u₁, u₂, u₃, u₄} D Q) where
  | ordinary (p : S.C₀ ≃ S.C₁)
  | extra (e : S.ExtraChoice)

variable (S : FullPolyGeneratedSource.{u, v, w, u₀, u₁, u₂, u₃, u₄} D Q)

/-- Output object of an ordinary or extra source choice. -/
def outputObject : S.Choice → S.C₁
  | .ordinary p => p (S.kummer₀ S.thetaPilotObject)
  | .extra e => S.extraOutput e

/-- The full-poly ordinary representative determined by Kummer conjugation. -/
def ordinaryEquiv : S.C₀ ≃ S.C₁ :=
  conjugateEquiv S.kummer₀ S.kummer₁ S.horizontal

@[simp]
theorem ordinary_output_eq_qPilot :
    S.outputObject (.ordinary S.ordinaryEquiv) =
      S.kummer₁ S.qPilotObject := by
  simp [outputObject, ordinaryEquiv, S.horizontalPilot]

/-- Convert the full-poly source into the actual generated-output data. -/
noncomputable def toGeneratedOutputData :
    GeneratedOutputData.{u, v, max u₄ (max u₂ u₃)} S.container where
  Output := S.Choice
  outputNonempty := ⟨.ordinary S.ordinaryEquiv⟩
  realize c := S.realize (S.outputObject c)
  support := S.support
  realize_eq_integral_outside c i vQ hv :=
    S.realize_eq_integral_outside _ i vQ hv
  realize_le_logShell c i := S.realize_le_logShell _ i

/-- The actual generated RHS bundle. -/
noncomputable def toGeneratedRHSData :
    GeneratedRHSData.{u, v, max u₄ (max u₂ u₃)} D where
  container := S.container
  proc_standard := S.proc_standard
  toRational_finite := S.toRational_finite
  toRational_infinite := S.toRational_infinite
  vol := S.vol
  hull := S.hull
  outputs := S.toGeneratedOutputData
  union_hullAdmissible := by
    intro i
    simpa [toGeneratedOutputData] using S.union_hullAdmissible i

/-- The source-shaped data construct one distinguished native output. -/
noncomputable def toGeneratedNativeSource :
    GeneratedNativeSource.{u, v, max u₄ (max u₂ u₃)} D Q where
  rhs := S.toGeneratedRHSData
  native := .ordinary S.ordinaryEquiv
  nativeVolume := by
    simpa [toGeneratedRHSData, toGeneratedOutputData,
      outputObject] using S.qVolume
  processionVol_mono := S.processionVol_mono

/-- The full-poly source closes the public numerical variant. -/
theorem corollary312Variant :
    Corollary312Variant S.toGeneratedNativeSource.toVariantData :=
  S.toGeneratedNativeSource.corollary312Variant

end FullPolyGeneratedSource
end IUTActualTypes
