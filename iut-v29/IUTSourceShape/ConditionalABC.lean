import IUTSourceShape.OrdinaryChoiceUnion
import IUTSourceShape.ABCStatement

namespace IUTSourceShape

universe u₀ u₁ u₂ u₃ u₄

structure DownstreamIUTIV (CTheta : ℝ) where
  abc_of_coefficient : -1 ≤ CTheta → ABCConjecture

variable {A₀ : Type u₀} {A₁ : Type u₁}
variable {C₀ : Type u₂} {C₁ : Type u₃}

theorem abc_of_full_poly_source
    (D : FullPolyPilotData.{u₀, u₁, u₂, u₃, u₄} A₀ A₁ C₀ C₁)
    {Q CTheta : ℝ}
    (hQ : 0 < Q)
    (hq : D.qSigned = -Q)
    (hupper : D.thetaSigned ≤ CTheta * Q)
    (R : DownstreamIUTIV CTheta) :
    ABCConjecture :=
  R.abc_of_coefficient (D.coefficient_ge_neg_one hQ hq hupper)

end IUTSourceShape
