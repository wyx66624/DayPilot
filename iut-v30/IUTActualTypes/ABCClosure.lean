/-
Copyright (c) 2026 ChatGPT. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ChatGPT
-/
import IUTActualTypes.QuantifierCorrectClosure
import IUTActualTypes.ABCStatement

/-!
# Quantifier-correct final closure to abc

This module gives the exact final theorem shape.  It deliberately requires a pointwise
IUT III family and a uniform downstream theorem.  Neither input is constructed by the
public IUT repository.
-/

namespace IUTActualTypes

open Iut

universe u v w z

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}
variable {Input : Type z}

/-- The exact final conditional theorem in the actual public Corollary 3.12 types. -/
theorem abc_of_pointwise_iut
    (F : PointwiseIUTIIIFamily.{u, v, w, z} (AG := AG) (TG := TG) Input)
    (R : UniformDownstream F ABCConjecture) :
    ABCConjecture :=
  R.target

/-- One package containing precisely the two universal constructions that a genuine
parameter-free proof must supply. -/
structure UniversalABCCertificate : Type
    (max (u + 1) (v + 1) (w + 1) (z + 1)) where
  family : PointwiseIUTIIIFamily.{u, v, w, z} (AG := AG) (TG := TG) Input
  downstream : UniformDownstream family ABCConjecture

namespace UniversalABCCertificate

/-- A fully inhabited universal certificate proves abc. -/
theorem abc (C : UniversalABCCertificate.{u, v, w, z}
    (AG := AG) (TG := TG) (Input := Input)) : ABCConjecture :=
  abc_of_pointwise_iut C.family C.downstream

end UniversalABCCertificate

end IUTActualTypes
