/-
Copyright (c) 2026 ChatGPT. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ChatGPT
-/
import IUTInhabitation.AdmissiblePrimeInhabitation
import IUTInhabitation.OrbicurveInhabitation

/-!
# Focused inhabitation boundary
-/

namespace IUTInhabitation

universe u z

/-- The two exact focused propositions requested by the research programme. -/
structure FocusedInhabitationResult
    {Input : Type z}
    (AG : Iut.AnabelianGeometry.{u})
    (G : GlobalCurveFamily.{u, z} Input) where
  admissiblePrime : AdmissiblePrimeFamilyExists G
  chosenPrime : ∀ x,
    Iut.AdmissiblePrimeData
      (G.globalCurve x).F
      (G.globalCurve x).E
      (G.globalCurve x).Fbar
      (G.globalCurve x).VBad
  orbicurve : OrbicurveFamilyExists AG G chosenPrime

/-- The remaining nonemptiness statement after the automatic Tate and cusp choices are
eliminated. -/
def FocusedInhabitationOpen
    {Input : Type z}
    (AG : Iut.AnabelianGeometry.{u})
    (G : GlobalCurveFamily.{u, z} Input) : Prop :=
  ∃ P : ∀ x,
      Iut.AdmissiblePrimeData
        (G.globalCurve x).F
        (G.globalCurve x).E
        (G.globalCurve x).Fbar
        (G.globalCurve x).VBad,
    OrbicurveCoreFamilyExists AG G P

end IUTInhabitation
