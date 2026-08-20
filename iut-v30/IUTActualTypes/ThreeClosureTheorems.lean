/-
Copyright (c) 2026 ChatGPT. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ChatGPT
-/
import IUTActualTypes.ABCClosure

/-!
# Exact formal types of the three missing closures

This module gives the three names requested by the research programme with the correct
pointwise quantifiers.  It proves the final composition theorem.  The module does not
construct an inhabitant of `ThreeClosureCertificate`; doing so is precisely the
remaining mathematics.
-/

set_option linter.checkUnivs false

namespace IUTActualTypes

open Iut

universe u v w z

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable {Input : Type z}

/-- A proof package containing exactly the three requested universal constructions. -/
structure ThreeClosureCertificate : Type
    (max (u + 1) (v + 1) (w + 1) (z + 1)) where
  /-- First closure: initial theta-data for every arithmetic input. -/
  actualInitialThetaDataOf :
    Input → InitialThetaData AG TG

  /-- The corresponding q-pilot scalar data.  This is separated because the public
  source structure is indexed by it. -/
  actualQPilotDataOf :
    ∀ x, QPilotData (actualInitialThetaDataOf x)

  /-- Second closure: actual IUT III output source for every input. -/
  actualIUTIIIOutputSourceOf :
    ∀ x, GeneratedNativeSource.{u, v, w}
      (actualInitialThetaDataOf x)
      (actualQPilotDataOf x)

  /-- Third closure: the uniform IUT IV theorem converting the pointwise Corollary 3.12
  family into the standard logarithmic abc conjecture. -/
  actualIUTIVDownstream :
    (∀ x,
      Corollary312Variant
        (actualIUTIIIOutputSourceOf x).toVariantData) →
      ABCConjecture

namespace ThreeClosureCertificate

/-- The pointwise IUT III family extracted from the three-closure package. -/
noncomputable def family
    (C : ThreeClosureCertificate.{u, v, w, z}
      (AG := AG) (TG := TG) (Input := Input)) :
    PointwiseIUTIIIFamily.{u, v, w, z} (AG := AG) (TG := TG) Input where
  data := C.actualInitialThetaDataOf
  qPilot := C.actualQPilotDataOf
  source := C.actualIUTIIIOutputSourceOf

/-- The third closure expressed as the generic uniform-downstream type. -/
noncomputable def downstream
    (C : ThreeClosureCertificate.{u, v, w, z}
      (AG := AG) (TG := TG) (Input := Input)) :
    UniformDownstream C.family ABCConjecture where
  close := C.actualIUTIVDownstream

/-- Complete formal composition of the three requested closures. -/
theorem abc_conjecture_of_three_closures
    (C : ThreeClosureCertificate.{u, v, w, z}
      (AG := AG) (TG := TG) (Input := Input)) :
    ABCConjecture :=
  abc_of_pointwise_iut C.family C.downstream

end ThreeClosureCertificate

/-- This is the exact final object whose construction would yield an unparameterized
Lean proof.  No definition of this constant is supplied because the public libraries do
not prove its existence. -/
def FinalCertificateType : Type
    (max (u + 1) (v + 1) (w + 1) (z + 1)) :=
  ThreeClosureCertificate.{u, v, w, z}
    (AG := AG) (TG := TG) (Input := Input)

end IUTActualTypes
