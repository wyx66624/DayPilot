import IUTSourceShape.FullPolyConjugation
import Mathlib

namespace IUTSourceShape

def boolSwapEquiv : Bool ≃ Bool where
  toFun b := !b
  invFun b := !b
  left_inv b := by cases b <;> rfl
  right_inv b := by cases b <;> rfl

@[simp] theorem boolSwapEquiv_false : boolSwapEquiv false = true := rfl

def restrictedCoric : Set (Bool ≃ Bool) := {Equiv.refl Bool}

theorem conjugate_not_mem_restricted :
    conjugate (Equiv.refl Bool) (Equiv.refl Bool) boolSwapEquiv ∉
      restrictedCoric := by
  intro h
  have heq :
      conjugate (Equiv.refl Bool) (Equiv.refl Bool) boolSwapEquiv =
        Equiv.refl Bool := by
    simpa [restrictedCoric] using h
  have hfalse := congrArg (fun e : Bool ≃ Bool => e false) heq
  simp [conjugate, boolSwapEquiv] at hfalse

end IUTSourceShape
