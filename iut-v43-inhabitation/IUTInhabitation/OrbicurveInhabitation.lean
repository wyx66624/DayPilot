/-
Copyright (c) 2026 ChatGPT. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ChatGPT
-/
import IUTInhabitation.CoreData

/-!
# Orbicurve inhabitation: eliminate the distinguished element and cusp choices

The public `Iut.OrbicurveData` asks for a core orbicurve, its covering square, a
rank-one quotient identification, a nonzero quotient element, and the corresponding
cusp. Once the geometric core/cover data and the quotient equivalence are supplied,
the last three choices are canonical: use the inverse image of `1 ∈ ZMod ℓ` and apply
`cuspOfQuotient`.
-/

set_option linter.checkUnivs false

namespace IUTInhabitation

open Iut NumberField OrbicurveDataSection

universe u z

variable (AG : AnabelianGeometry.{u})
variable (G : GlobalFieldCurveComponent.{u})
variable (P : AdmissiblePrimeData G.F G.E G.Fbar G.VBad)

/-- The genuinely geometric part of `Iut.OrbicurveData`. -/
structure OrbicurveCoreCoverData : Type (u + 1) where
  CKu : AG.Orbicurve ↥P.torsionField
  CKu_type : AG.IsTypeOneEllTorsPM P.ℓ CKu
  CKu_core : AG.HasCore CKu (CK AG G.F G.E G.Fbar G.VBad P)
  XKu : AG.Orbicurve ↥P.torsionField
  XKu_type : AG.IsTypeOneEllTors P.ℓ XKu
  XKu_to_XK : AG.Cover XKu (XK AG G.F G.E G.Fbar G.VBad P)
  XKu_to_CKu : AG.Cover XKu CKu
  XK_to_CK :
    AG.Cover (XK AG G.F G.E G.Fbar G.VBad P)
      (CK AG G.F G.E G.Fbar G.VBad P)
  CKu_to_CK : AG.Cover CKu (CK AG G.F G.E G.Fbar G.VBad P)
  diagram_cartesian :
    AG.IsCartesianSquare XKu_to_XK XK_to_CK XKu_to_CKu CKu_to_CK
  QIso : AG.RankOneQuotient CKu P.ℓ ≃ ZMod P.ℓ

namespace OrbicurveCoreCoverData

variable {AG G P}

/-- Canonical nonzero quotient element. -/
noncomputable def canonicalQ
    (C : OrbicurveCoreCoverData AG G P) :
    AG.RankOneQuotient C.CKu P.ℓ :=
  C.QIso.symm 1

/-- The canonical quotient element is nonzero. -/
theorem canonicalQ_ne_zero
    (C : OrbicurveCoreCoverData AG G P) :
    C.QIso C.canonicalQ ≠ 0 := by
  letI : Fact P.ℓ.Prime := ⟨P.ℓ_prime⟩
  simp [canonicalQ]

/-- Canonical distinguished cusp. -/
noncomputable def canonicalEpsilon
    (C : OrbicurveCoreCoverData AG G P) :
    AG.Cusp C.CKu :=
  AG.cuspOfQuotient C.CKu P.ℓ C.canonicalQ

/-- Assemble the exact public orbicurve record. -/
noncomputable def toOrbicurveData
    (C : OrbicurveCoreCoverData AG G P) :
    OrbicurveData AG G.F G.E G.Fbar G.VBad P where
  CKu := C.CKu
  CKu_type := C.CKu_type
  CKu_core := C.CKu_core
  XKu := C.XKu
  XKu_type := C.XKu_type
  XKu_to_XK := C.XKu_to_XK
  XKu_to_CKu := C.XKu_to_CKu
  XK_to_CK := C.XK_to_CK
  CKu_to_CK := C.CKu_to_CK
  diagram_cartesian := C.diagram_cartesian
  QIso := C.QIso
  q := C.canonicalQ
  q_ne_zero := C.canonicalQ_ne_zero
  epsilon := C.canonicalEpsilon
  epsilon_spec := rfl

/-- Forget only the canonical quotient element and cusp. -/
def ofOrbicurveData
    (O : OrbicurveData AG G.F G.E G.Fbar G.VBad P) :
    OrbicurveCoreCoverData AG G P where
  CKu := O.CKu
  CKu_type := O.CKu_type
  CKu_core := O.CKu_core
  XKu := O.XKu
  XKu_type := O.XKu_type
  XKu_to_XK := O.XKu_to_XK
  XKu_to_CKu := O.XKu_to_CKu
  XK_to_CK := O.XK_to_CK
  CKu_to_CK := O.CKu_to_CK
  diagram_cartesian := O.diagram_cartesian
  QIso := O.QIso

/-- Nonemptiness of the public orbicurve record is equivalent to nonemptiness of the
purely geometric core/cover record. -/
theorem nonempty_orbicurveData_iff :
    Nonempty (OrbicurveData AG G.F G.E G.Fbar G.VBad P) ↔
      Nonempty (OrbicurveCoreCoverData AG G P) := by
  constructor
  · rintro ⟨O⟩
    exact ⟨ofOrbicurveData O⟩
  · rintro ⟨C⟩
    exact ⟨C.toOrbicurveData⟩

end OrbicurveCoreCoverData

/-- Exact pointwise geometric-core existence target. -/
def OrbicurveCoreFamilyExists
    {Input : Type z}
    (AG : AnabelianGeometry.{u})
    (C : GlobalCurveFamily.{u, z} Input)
    (P : ∀ x,
      AdmissiblePrimeData
        (C.globalCurve x).F
        (C.globalCurve x).E
        (C.globalCurve x).Fbar
        (C.globalCurve x).VBad) : Prop :=
  ∀ x, Nonempty (OrbicurveCoreCoverData AG (C.globalCurve x) (P x))

/-- The actual core/cover theorem supplies the public orbicurve family. -/
theorem orbicurveFamilyExists_of_core
    {Input : Type z}
    {AG : AnabelianGeometry.{u}}
    {C : GlobalCurveFamily.{u, z} Input}
    {P : ∀ x,
      AdmissiblePrimeData
        (C.globalCurve x).F
        (C.globalCurve x).E
        (C.globalCurve x).Fbar
        (C.globalCurve x).VBad}
    (h : OrbicurveCoreFamilyExists AG C P) :
    OrbicurveFamilyExists AG C P := by
  intro x
  rcases h x with ⟨K⟩
  exact ⟨K.toOrbicurveData⟩

end IUTInhabitation
