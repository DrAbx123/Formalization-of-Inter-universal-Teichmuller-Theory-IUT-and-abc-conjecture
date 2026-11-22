import LeanFormal.IUT.Foundations.NumberField.LocalQParameter
import LeanFormal.IUT.IUTI.InitialTheta.ArithmeticData
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3139: C2 natural candidate — global units of F_mod into the actual finite-place completions

C2 is the finite-place conjugate channel of the copy action: a map from the
global units of `F_mod` to local units (IUT III:616-620, Fig. I.5).  The tree
has the actual finite-place completions `NumberFieldFinitePlace.Completion` and
the actual completion embeddings; this file constructs the natural candidate

  `sourceFmodUnitsToFiniteCompletion A W : (A.Fmod)^x ->* (K_W)^x`

by sending a global unit through the completion embedding and taking units.  It
is a group homomorphism by construction, and it is the candidate that must be
compared with the prime-strip local units (the missing placeToMod/cusp
identification owned by shehdd/stage4).

**Component, not paper object.**  Named consumer: `SourceConjugateLocalUnitMap`
(task-55 residual) and the finite-place copy channel.  No sorry/axiom/True/
PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139C2FiniteCompletionUnitsActual

open LeanFormal.IUT

universe u

namespace C2Finite

variable (A : LeanFormal.IUT.InitialThetaArithmeticData.{u} l)
variable (W : NumberField.FinitePlace A.Fmod)

/-- The natural candidate for the finite-place conjugate channel: a global unit
of `F_mod` maps to the unit of its image in the actual completion at the finite
place `W`. -/
noncomputable def sourceFmodUnitsToFiniteCompletion :
    (A.Fmod)ˣ →* (NumberFieldFinitePlace.Completion W)ˣ :=
  Units.map (algebraMap A.Fmod (NumberFieldFinitePlace.Completion W)).toMonoidHom

/-- The candidate channel is a group homomorphism (multiplicativity). -/
theorem sourceFmodUnitsToFiniteCompletion_mul (u w : (A.Fmod)ˣ) :
    sourceFmodUnitsToFiniteCompletion A W (u * w) =
      sourceFmodUnitsToFiniteCompletion A W u *
        sourceFmodUnitsToFiniteCompletion A W w :=
  map_mul (sourceFmodUnitsToFiniteCompletion A W) u w

/-- The candidate channel sends the unit to the unit. -/
theorem sourceFmodUnitsToFiniteCompletion_one :
    sourceFmodUnitsToFiniteCompletion A W 1 = 1 :=
  map_one (sourceFmodUnitsToFiniteCompletion A W)

/-- The value of the candidate channel is the unit of the actual completion
embedding of the global unit. -/
theorem sourceFmodUnitsToFiniteCompletion_val (u : (A.Fmod)ˣ) :
    (sourceFmodUnitsToFiniteCompletion A W u :
      NumberFieldFinitePlace.Completion W) =
      algebraMap A.Fmod (NumberFieldFinitePlace.Completion W) (u : A.Fmod) := rfl

end C2Finite

end LeanFormal.IUT.XiFPaper.S3139C2FiniteCompletionUnitsActual

end
