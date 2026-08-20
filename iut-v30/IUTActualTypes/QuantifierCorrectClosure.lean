/-
Copyright (c) 2026 ChatGPT. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ChatGPT
-/
import IUTActualTypes.GeneratedSource

/-!
# Quantifier-correct shape of a parameter-free IUT/abc closure

A single closed `InitialThetaData` object cannot prove a universal Diophantine
statement.  The initial theta-data, q-pilot data, and IUT III source have to be
constructed as a family indexed by every arithmetic input to which the final theorem
is applied (and, in the IUT IV argument, by epsilon and the auxiliary choices).

This module records the correct dependent type and proves the corresponding universal
Corollary 3.12 theorem.  It also gives a finite logical countermodel showing why the
existence of one certificate cannot replace a family of certificates.
-/

set_option linter.checkUnivs false

namespace IUTActualTypes

open Iut

universe u v w z

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}

/-- A family of actual public-type IUT III sources, one for every input. -/
structure PointwiseIUTIIIFamily (Input : Type z) :
    Type (max (u + 1) (v + 1) (w + 1) (z + 1)) where
  data : Input → InitialThetaData AG TG
  qPilot : ∀ x, QPilotData (data x)
  source : ∀ x, GeneratedNativeSource.{u, v, w} (data x) (qPilot x)

namespace PointwiseIUTIIIFamily

variable {Input : Type z}

/-- A pointwise source family proves Corollary 3.12 for every input. -/
theorem corollary312Variant
    (F : PointwiseIUTIIIFamily.{u, v, w, z} (AG := AG) (TG := TG) Input)
    (x : Input) :
    Corollary312Variant (F.source x).toVariantData :=
  (F.source x).corollary312Variant

/-- Uniform form of the previous theorem. -/
theorem corollary312Variant_all
    (F : PointwiseIUTIIIFamily.{u, v, w, z} (AG := AG) (TG := TG) Input) :
    ∀ x, Corollary312Variant (F.source x).toVariantData :=
  fun x => F.corollary312Variant x

end PointwiseIUTIIIFamily

/-- The downstream theorem must consume the whole pointwise family of Corollary 3.12
statements. -/
structure UniformDownstream
    {Input : Type z}
    (F : PointwiseIUTIIIFamily.{u, v, w, z} (AG := AG) (TG := TG) Input)
    (Target : Prop) : Type (max u v w z) where
  close : (∀ x, Corollary312Variant (F.source x).toVariantData) → Target

namespace UniformDownstream

variable {Input : Type z}
variable {F : PointwiseIUTIIIFamily.{u, v, w, z} (AG := AG) (TG := TG) Input}
variable {Target : Prop}

/-- A pointwise IUT III family together with one uniform downstream theorem proves the
universal target. -/
theorem target (R : UniformDownstream F Target) : Target :=
  R.close F.corollary312Variant_all

end UniformDownstream

namespace OneCertificateCountermodel

/-- A toy pointwise certificate available only at one Boolean input. -/
def Certificate (b : Bool) : Prop := b = false

theorem one_certificate_exists : ∃ b, Certificate b :=
  ⟨false, rfl⟩

theorem not_all_certificates : ¬ ∀ b, Certificate b := by
  intro h
  have := h true
  simp [Certificate] at this

/-- Therefore existence of one closed certificate does not imply availability of the
pointwise family required for a universal theorem. -/
theorem exists_does_not_imply_forall :
    (∃ b, Certificate b) ∧ ¬ (∀ b, Certificate b) :=
  ⟨one_certificate_exists, not_all_certificates⟩

end OneCertificateCountermodel

end IUTActualTypes
