/-
Copyright (c) 2026 ChatGPT. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ChatGPT
-/
import Iut.Cor312.ThetaData.Orbicurve

/-!
# Global curve data and the two focused inhabitation propositions
-/

set_option linter.checkUnivs false

namespace IUTInhabitation

open Iut NumberField WeierstrassCurve OrbicurveDataSection

universe u z

/-- Global number-field and elliptic-curve data consumed by the admissible-prime and
orbicurve constructions. -/
structure GlobalFieldCurveComponent : Type (u + 1) where
  F : Type u
  [fieldF : Field F]
  [numberFieldF : NumberField F]
  Fbar : Type u
  [fieldFbar : Field Fbar]
  [algebraFbar : Algebra F Fbar]
  E : WeierstrassCurve F
  [isElliptic : E.IsElliptic]
  VBad : Set (FinitePlace ↥(fieldOfModuli F E))

namespace GlobalFieldCurveComponent

attribute [instance] fieldF numberFieldF fieldFbar algebraFbar isElliptic

end GlobalFieldCurveComponent

/-- A pointwise family of global curve data. -/
structure GlobalCurveFamily (Input : Type z) : Type (max (u + 1) (z + 1)) where
  globalCurve : Input → GlobalFieldCurveComponent.{u}

/-- Exact focused target 1. -/
def AdmissiblePrimeFamilyExists
    {Input : Type z} (G : GlobalCurveFamily.{u, z} Input) : Prop :=
  ∀ x : Input,
    Nonempty
      (AdmissiblePrimeData
        (G.globalCurve x).F
        (G.globalCurve x).E
        (G.globalCurve x).Fbar
        (G.globalCurve x).VBad)

/-- Exact focused target 2. -/
def OrbicurveFamilyExists
    {Input : Type z}
    (AG : AnabelianGeometry.{u})
    (G : GlobalCurveFamily.{u, z} Input)
    (P : ∀ x,
      AdmissiblePrimeData
        (G.globalCurve x).F
        (G.globalCurve x).E
        (G.globalCurve x).Fbar
        (G.globalCurve x).VBad) : Prop :=
  ∀ x : Input,
    Nonempty
      (OrbicurveData AG
        (G.globalCurve x).F
        (G.globalCurve x).E
        (G.globalCurve x).Fbar
        (G.globalCurve x).VBad
        (P x))

end IUTInhabitation
