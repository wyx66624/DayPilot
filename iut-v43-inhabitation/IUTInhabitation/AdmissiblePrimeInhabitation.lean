/-
Copyright (c) 2026 ChatGPT. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ChatGPT
-/
import IUTInhabitation.CoreData
import IUTInhabitation.PrimeSelection

/-!
# Admissible-prime inhabitation: exact construction and remaining large-image theorem

This module uses the actual public `Iut.AdmissiblePrimeData` type.

It eliminates the Tate-parameter choice from the input: once the local norm hypotheses
`‖12‖ = 1` and `1 < ‖j(E)‖` are supplied, the unique Tate parameter is selected by the
public `TateCurvesTheta` theorem. The representation, its large image, openness, the
chosen torsion basis, and the local coprimality statements remain genuine mathematical
inputs.
-/

set_option linter.checkUnivs false

namespace IUTInhabitation

open Iut NumberField WeierstrassCurve TateCurvesTheta

universe u z

variable (G : GlobalFieldCurveComponent.{u})

/-- The global/Galois part of admissible-prime data. -/
structure AdmissiblePrimeRepresentationCore : Type (u + 1) where
  ℓ : ℕ
  ℓ_prime : ℓ.Prime
  five_le : 5 ≤ ℓ
  torsionBasis :
    AddSubgroup.torsionBy
        (Affine.Point (Affine.baseChange G.E G.Fbar)) ℓ ≃+
      (Fin 2 → ZMod ℓ)
  rep :
    (G.Fbar ≃ₐ[G.F] G.Fbar) →*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod ℓ)
  rep_spec : ∀ (σ : G.Fbar ≃ₐ[G.F] G.Fbar)
    (P : AddSubgroup.torsionBy
      (Affine.Point (Affine.baseChange G.E G.Fbar)) ℓ),
    torsionBasis
        ⟨galPointMap G.F G.E G.Fbar σ P.1,
          galPointMap_torsionBy G.F G.E G.Fbar σ P.2⟩ =
      (rep σ : Matrix (Fin 2) (Fin 2) (ZMod ℓ)).mulVec
        (torsionBasis P)
  sl_le_range :
    ∀ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod ℓ),
      A.toGL ∈ rep.range
  ker_isOpen : IsOpen (rep.ker : Set (G.Fbar ≃ₐ[G.F] G.Fbar))
  galois_deg_prime : IsGaloisOfDegreePrimeTo G.F G.E ℓ
  residueChar_coprime :
    ∀ v ∈ G.VBad, Nat.Coprime ℓ (residueChar v)

namespace AdmissiblePrimeRepresentationCore

variable {G}

/-- Local inputs from which the public unique Tate parameter is generated. -/
structure GeneratedLocalTateData
    (R : AdmissiblePrimeRepresentationCore G) : Type (u + 1) where
  h12 : ∀ w (hw : w ∈ badPlacesOver G.F G.E G.VBad),
    ‖(12 : localCompletion w)‖ = 1
  j_large : ∀ w (hw : w ∈ badPlacesOver G.F G.E G.VBad),
    1 < ‖FinitePlace.embedding w.maximalIdeal G.E.j‖
  unif : ∀ w (hw : w ∈ badPlacesOver G.F G.E G.VBad),
    localCompletion w
  unif_isUniformizer : ∀ w (hw : w ∈ badPlacesOver G.F G.E G.VBad),
    IsUniformizer (unif w hw)

namespace GeneratedLocalTateData

variable {R : AdmissiblePrimeRepresentationCore G}

/-- The unique Tate parameter supplied by the public Tate-curve theorem. -/
noncomputable def chosenTate
    (L : GeneratedLocalTateData R)
    (w : FinitePlace G.F)
    (hw : w ∈ badPlacesOver G.F G.E G.VBad) :
    TateParameter (localCompletion w) :=
  Classical.choose
    (TateParameter.existsUnique_splitMultiplicative_tateParameter
      (L.h12 w hw) (L.j_large w hw))

/-- The selected parameter has the required j-invariant. -/
theorem chosenTate_tateJ
    (L : GeneratedLocalTateData R)
    (w : FinitePlace G.F)
    (hw : w ∈ badPlacesOver G.F G.E G.VBad) :
    (L.chosenTate w hw).tateJ =
      FinitePlace.embedding w.maximalIdeal G.E.j :=
  (Classical.choose_spec
    (TateParameter.existsUnique_splitMultiplicative_tateParameter
      (L.h12 w hw) (L.j_large w hw))).1

/-- The remaining local arithmetic condition after the Tate parameter is generated. -/
def PrimeToChosenOrders (L : GeneratedLocalTateData R) : Prop :=
  ∀ w (hw : w ∈ badPlacesOver G.F G.E G.VBad),
    ((L.chosenTate w hw).toOrdered
      (L.unif_isUniformizer w hw)).PrimeToOrder R.ℓ

end GeneratedLocalTateData

/-- Assemble the exact public admissible-prime record. -/
noncomputable def toAdmissiblePrimeData
    (R : AdmissiblePrimeRepresentationCore G)
    (L : GeneratedLocalTateData R)
    (hPrimeTo : L.PrimeToChosenOrders) :
    AdmissiblePrimeData G.F G.E G.Fbar G.VBad where
  ℓ := R.ℓ
  ℓ_prime := R.ℓ_prime
  five_le := R.five_le
  torsionBasis := R.torsionBasis
  rep := R.rep
  rep_spec := R.rep_spec
  sl_le_range := R.sl_le_range
  ker_isOpen := R.ker_isOpen
  galois_deg_prime := R.galois_deg_prime
  residueChar_coprime := R.residueChar_coprime
  tate := L.chosenTate
  tateJ_eq := L.chosenTate_tateJ
  unif := L.unif
  unif_isUniformizer := L.unif_isUniformizer
  q_order_coprime := hPrimeTo

/-- The focused construction theorem. -/
theorem nonempty_admissiblePrimeData
    (R : AdmissiblePrimeRepresentationCore G)
    (L : GeneratedLocalTateData R)
    (hPrimeTo : L.PrimeToChosenOrders) :
    Nonempty (AdmissiblePrimeData G.F G.E G.Fbar G.VBad) :=
  ⟨R.toAdmissiblePrimeData L hPrimeTo⟩

end AdmissiblePrimeRepresentationCore

/-- Public admissible-prime data whose selected prime is definitionally tied to an
externally chosen natural number. -/
structure AdmissiblePrimeAt
    (G : GlobalFieldCurveComponent.{u}) (ℓ : ℕ) : Type (u + 1) where
  data : AdmissiblePrimeData G.F G.E G.Fbar G.VBad
  prime_eq : data.ℓ = ℓ

/-- A precise eventual large-image theorem, sufficient for pointwise inhabitation. -/
structure EventualAdmissiblePrimeFamily
    {Input : Type z} (C : GlobalCurveFamily.{u, z} Input) where
  threshold : Input → ℕ
  exceptional : Input → Finset ℕ
  construct : ∀ x ℓ,
    ℓ.Prime → threshold x < ℓ → ℓ ∉ exceptional x →
      Nonempty (AdmissiblePrimeAt (C.globalCurve x) ℓ)

namespace EventualAdmissiblePrimeFamily

/-- Finite prime avoidance converts an eventual theorem into actual pointwise
inhabitation. -/
theorem admissiblePrimeFamilyExists
    {Input : Type z} {C : GlobalCurveFamily.{u, z} Input}
    (A : EventualAdmissiblePrimeFamily C) :
    AdmissiblePrimeFamilyExists C := by
  intro x
  rcases exists_prime_above_not_mem (A.threshold x) (A.exceptional x) with
    ⟨ℓ, hℓ, hlarge, hex⟩
  rcases A.construct x ℓ hℓ hlarge hex with ⟨W⟩
  exact ⟨W.data⟩

end EventualAdmissiblePrimeFamily

end IUTInhabitation
