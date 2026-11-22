import tmp.sheaf.xif.paper.S3139FirstTriangleFieldACResidualActual
import LeanFormal.IUT.Foundations.AlgebraicGeometry.InfinitePlaceLogDictionary
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

/-!
# S3139: field (C) — actual archimedean Real realification of F_mod^x (part 1)

The task-27 formulation of the (Ind2) copy action used a ring embedding
`F_mod -> Real` as a modeling bridge.  This file constructs the *actual
archimedean realification* of `F_mod^x` from the actual arithmetic data
(IUT III:616-620, Fig. I.5; Formalization of IUT (2026-04) :514-524):

* `infinitePlaceLog v : Additive (v.Completion)^x ->+ R` is the production
  actual additive norm-log at an infinite place (`InfinitePlaceLogDictionary`);
* embedding the actual `F_mod` into its completion by `algebraMap` and taking
  units gives the actual additive log `sourceFmodArchimedeanLog A v`;
* exponentiating gives the actual multiplicative Real scalar character
  `sourceFmodArchimedeanScalarCharacter A v : (A.Fmod)^x ->* R^x`.

`SourceInfinitePlaceChoice` records the one datum not determined by
`InitialThetaArithmeticData`: the infinite place used for the realification
(no infinite-place field exists in the actual input; page refs III:616-620,
Fig. I.5).

**Component, not paper object.**  Named future consumer: the copy-action data
`SourceInd2CopyActionData` and the lattice/mainline q/Theta readouts.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139FieldCArchimedeanLogActual

open LeanFormal.IUT
open LeanFormal.IUT.InfinitePlaceLogDictionary

universe ua uv upi umon ui u

variable {l : PrimeGeFive} {V : Type uv}
variable (A : LeanFormal.IUT.InitialThetaArithmeticData.{u} l)
variable (v : NumberField.InfinitePlace A.Fmod)

/-- The actual additive archimedean log of a unit of `F_mod`: embed the unit
into the completion at the infinite place and apply the production additive
norm-log. -/
noncomputable def sourceFmodArchimedeanLog : Additive (A.Fmod)ˣ →+ ℝ where
  toFun u := infinitePlaceLog v (Additive.ofMul
    ((Units.map (algebraMap A.Fmod v.Completion).toMonoidHom) u.toMul))
  map_zero' := by
    show infinitePlaceLog v (Additive.ofMul
      ((Units.map (algebraMap A.Fmod v.Completion).toMonoidHom)
        ((0 : Additive (A.Fmod)ˣ).toMul))) = 0
    have h : Additive.ofMul ((Units.map
        (algebraMap A.Fmod v.Completion).toMonoidHom)
          ((0 : Additive (A.Fmod)ˣ).toMul)) = 0 := by
      rw [show (0 : Additive (A.Fmod)ˣ).toMul = (1 : (A.Fmod)ˣ) from rfl, map_one]
      rfl
    rw [h, map_zero]
  map_add' := by
    intro x y
    show infinitePlaceLog v (Additive.ofMul
      ((Units.map (algebraMap A.Fmod v.Completion).toMonoidHom)
        ((x + y).toMul))) =
      infinitePlaceLog v (Additive.ofMul
        ((Units.map (algebraMap A.Fmod v.Completion).toMonoidHom) x.toMul)) +
      infinitePlaceLog v (Additive.ofMul
        ((Units.map (algebraMap A.Fmod v.Completion).toMonoidHom) y.toMul))
    have h : Additive.ofMul ((Units.map
        (algebraMap A.Fmod v.Completion).toMonoidHom)
          ((x + y).toMul)) =
        Additive.ofMul ((Units.map
          (algebraMap A.Fmod v.Completion).toMonoidHom) x.toMul) +
        Additive.ofMul ((Units.map
          (algebraMap A.Fmod v.Completion).toMonoidHom) y.toMul) := by
      rw [show (x + y).toMul = x.toMul * y.toMul from rfl, map_mul]
      rfl
    rw [h, map_add]

theorem sourceFmodArchimedeanLog_apply (u : (A.Fmod)ˣ) :
    sourceFmodArchimedeanLog A v (Additive.ofMul u) =
      infinitePlaceLog v (Additive.ofMul (Units.map
        (algebraMap A.Fmod v.Completion).toMonoidHom u)) := rfl

/-- The actual multiplicative Real scalar character of `F_mod^x` obtained by
exponentiating the actual archimedean additive log. -/
noncomputable def sourceFmodArchimedeanScalarCharacter : (A.Fmod)ˣ →* ℝˣ where
  toFun u := Units.mk0
    (Real.exp (sourceFmodArchimedeanLog A v (Additive.ofMul u)))
    (ne_of_gt (Real.exp_pos _))
  map_one' := by
    apply Units.ext
    simp
  map_mul' := by
    intro u w
    apply Units.ext
    have h1 : Additive.ofMul (u * w) =
        Additive.ofMul u + Additive.ofMul w := rfl
    show Real.exp (sourceFmodArchimedeanLog A v (Additive.ofMul (u * w))) =
      (Units.mk0 (Real.exp (sourceFmodArchimedeanLog A v (Additive.ofMul u))) _ *
        Units.mk0 (Real.exp (sourceFmodArchimedeanLog A v (Additive.ofMul w))) _ : ℝ)
    rw [h1, map_add, Real.exp_add]
    simp [Units.val_mul, Units.val_mk0]

theorem sourceFmodArchimedeanScalarCharacter_apply (u : (A.Fmod)ˣ) :
    (sourceFmodArchimedeanScalarCharacter A v u : ℝ) =
      Real.exp (sourceFmodArchimedeanLog A v (Additive.ofMul u)) := rfl

/-- The archimedean realification choice datum: an infinite place of the actual
`F_mod`.  `InitialThetaArithmeticData` does not determine one, so it is
supplied explicitly (III:616-620, Fig. I.5). -/
def SourceInfinitePlaceChoice (A : LeanFormal.IUT.InitialThetaArithmeticData.{u} l) :
    Type u :=
  NumberField.InfinitePlace A.Fmod

/-- Every supplied infinite-place choice yields the actual Real scalar
character of the copies. -/
noncomputable def sourceInfinitePlaceScalarCharacter
    (A : LeanFormal.IUT.InitialThetaArithmeticData.{u} l)
    (c : SourceInfinitePlaceChoice A) : (A.Fmod)ˣ →* ℝˣ :=
  sourceFmodArchimedeanScalarCharacter A c

end LeanFormal.IUT.XiFPaper.S3139FieldCArchimedeanLogActual

end
