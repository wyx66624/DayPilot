import IUTSourceShape.FullPolyConjugation
import Mathlib

namespace IUTSourceShape

universe u₀ u₁ u₂ u₃ u₄

structure FullPolyPilotData
    (A₀ : Type u₀) (A₁ : Type u₁)
    (C₀ : Type u₂) (C₁ : Type u₃) where
  kummer₀ : A₀ ≃ C₀
  kummer₁ : A₁ ≃ C₁
  horizontal : A₀ ≃ A₁
  thetaPilot : A₀
  qPilot : A₁
  horizontalPilot : horizontal thetaPilot = qPilot
  ExtraChoice : Type u₄
  extraOutput : ExtraChoice → C₁
  volume : Set C₁ → ℝ
  volume_mono : Monotone volume
  qSigned : ℝ
  qPilotVolume : volume {kummer₁ qPilot} = qSigned

namespace FullPolyPilotData

variable {A₀ : Type u₀} {A₁ : Type u₁}
variable {C₀ : Type u₂} {C₁ : Type u₃}

inductive Choice (D : FullPolyPilotData A₀ A₁ C₀ C₁) where
  | ordinary (p : C₀ ≃ C₁)
  | extra (e : D.ExtraChoice)

variable (D : FullPolyPilotData A₀ A₁ C₀ C₁)

def output : D.Choice → C₁
  | .ordinary p => p (D.kummer₀ D.thetaPilot)
  | .extra e => D.extraOutput e

def thetaRegion : Set C₁ := Set.range D.output

def ordinaryWitness : C₀ ≃ C₁ :=
  conjugate D.kummer₀ D.kummer₁ D.horizontal

@[simp] theorem ordinaryWitness_output :
    D.output (.ordinary D.ordinaryWitness) = D.kummer₁ D.qPilot := by
  simp [output, ordinaryWitness, D.horizontalPilot]

theorem singleton_qPilot_subset_thetaRegion :
    ({D.kummer₁ D.qPilot} : Set C₁) ⊆ D.thetaRegion := by
  intro x hx
  have hx' : x = D.kummer₁ D.qPilot := by simpa using hx
  subst x
  exact ⟨.ordinary D.ordinaryWitness, D.ordinaryWitness_output⟩

def thetaSigned : ℝ := D.volume D.thetaRegion

theorem bridge : D.qSigned ≤ D.thetaSigned := by
  calc
    D.qSigned = D.volume {D.kummer₁ D.qPilot} := D.qPilotVolume.symm
    _ ≤ D.volume D.thetaRegion :=
      D.volume_mono D.singleton_qPilot_subset_thetaRegion
    _ = D.thetaSigned := rfl

theorem coefficient_ge_neg_one
    {Q CTheta : ℝ}
    (hQ : 0 < Q)
    (hq : D.qSigned = -Q)
    (hupper : D.thetaSigned ≤ CTheta * Q) :
    -1 ≤ CTheta := by
  have hbridge : -Q ≤ D.thetaSigned := by
    calc
      -Q = D.qSigned := hq.symm
      _ ≤ D.thetaSigned := D.bridge
  nlinarith

end FullPolyPilotData
end IUTSourceShape
