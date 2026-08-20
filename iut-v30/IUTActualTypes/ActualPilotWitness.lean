import Iut.Cor312.Statement

/-!
# Actual-region witness against the public IUT Corollary 3.12 types

This module removes all auxiliary source types (`A₀`, `A₁`, `C₀`, `C₁`) from the
numerical bridge.  The witness is a family of actual admissible regions in the public
large-volume container.

The theorem is intentionally one-way: the public repository does not construct such a
witness from Hodge theaters or the multiradial algorithm.
-/

namespace IUTActualTypes

open Iut

universe u v

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}

/-- The minimal object-level certificate in the actual public Corollary 3.12 types. -/
structure ActualPilotWitness
    (X : Corollary312VariantData.{u, v} AG TG) : Type (max u v) where
  /-- A capsule-indexed family of actual admissible regions representing the native
  q-pilot image. -/
  region : ∀ i, X.rhsData.container.AdmissibleRegion i
  /-- The native region is an actual member of the supplied theta-pilot union. -/
  region_le_thetaPilot :
    ∀ i, region i ≤ X.rhsData.thetaPilot i
  /-- Its procession-normalized volume is the public q-pilot left-hand side. -/
  qVolume :
    X.rhsData.vol.processionVol region = X.qPilot.lhs
  /-- Monotonicity on the specific good families used by the argument.  The public
  `LogVolumeData` interface deliberately omits a global law on junk regions. -/
  processionVol_mono :
    ∀ {R S : ∀ i, X.rhsData.container.AdmissibleRegion i},
      (∀ i, R i ≤ S i) →
        X.rhsData.vol.processionVol R ≤
          X.rhsData.vol.processionVol S

namespace ActualPilotWitness

variable {X : Corollary312VariantData.{u, v} AG TG}

/-- An actual native q-pilot witness closes the public numerical variant. -/
theorem corollary312Variant (W : ActualPilotWitness X) :
    Corollary312Variant X := by
  apply (corollary312Variant_iff X).2
  have htheta : ∀ i, X.rhsData.thetaPilot i ≤ X.rhsData.thetaHull i := by
    intro i
    change X.rhsData.thetaPilot i ≤
      X.rhsData.hull.hullAdmissible (X.rhsData.thetaPilot i)
    exact X.rhsData.hull.le_hullAdmissible
      (X.rhsData.thetaPilot_hullAdmissible i)
  have hregion : ∀ i, W.region i ≤ X.rhsData.thetaHull i := by
    intro i
    exact (W.region_le_thetaPilot i).trans (htheta i)
  calc
    X.qPilot.lhs = X.rhsData.vol.processionVol W.region := W.qVolume.symm
    _ ≤ X.rhsData.vol.processionVol X.rhsData.thetaHull :=
      W.processionVol_mono hregion
    _ = X.rhsData.rhs := rfl

end ActualPilotWitness
end IUTActualTypes
