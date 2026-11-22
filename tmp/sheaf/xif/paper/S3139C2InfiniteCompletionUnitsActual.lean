import tmp.sheaf.xif.paper.S3139FieldCArchimedeanLogActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3139: C2 natural candidate — global units of F_mod into the actual archimedean completions

The archimedean companion of `S3139C2FiniteCompletionUnitsActual`: a global unit
of `F_mod` maps to the unit of its image in the completion at an infinite place,
and the field-(C) actual archimedean log is exactly the production archimedean
log of that image (IUT III:616-620, Fig. I.5).  This identifies the two
constructions: the Real realification of `F_mod^x` is the archimedean instance
of the same global-units-to-local-units channel.

**Component, not paper object.**  Named consumers: `SourceArchimedeanRealification`,
`SourceInd2CopyActionData` and the lattice/mainline q/Theta readouts.  No
sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139C2InfiniteCompletionUnitsActual

open LeanFormal.IUT
open LeanFormal.IUT.InfinitePlaceLogDictionary
open LeanFormal.IUT.XiFPaper.S3139FieldCArchimedeanLogActual

universe u

namespace C2Infinite

variable (A : LeanFormal.IUT.InitialThetaArithmeticData.{u} l)
variable (W : NumberField.InfinitePlace A.Fmod)

/-- The natural candidate for the archimedean conjugate channel: a global unit
of `F_mod` maps to the unit of its image in the actual completion at the
infinite place `W`. -/
noncomputable def sourceFmodUnitsToInfiniteCompletion :
    (A.Fmod)ˣ →* (W.Completion)ˣ :=
  Units.map (algebraMap A.Fmod W.Completion).toMonoidHom

/-- The candidate channel is a group homomorphism (multiplicativity). -/
theorem sourceFmodUnitsToInfiniteCompletion_mul (u w : (A.Fmod)ˣ) :
    sourceFmodUnitsToInfiniteCompletion A W (u * w) =
      sourceFmodUnitsToInfiniteCompletion A W u *
        sourceFmodUnitsToInfiniteCompletion A W w :=
  map_mul (sourceFmodUnitsToInfiniteCompletion A W) u w

/-- The candidate channel sends the unit to the unit. -/
theorem sourceFmodUnitsToInfiniteCompletion_one :
    sourceFmodUnitsToInfiniteCompletion A W 1 = 1 :=
  map_one (sourceFmodUnitsToInfiniteCompletion A W)

/-- The field-(C) actual archimedean log is the production archimedean log of
the local image of the global unit. -/
theorem sourceFmodArchimedeanLog_eq_infinitePlaceLog (u : (A.Fmod)ˣ) :
    sourceFmodArchimedeanLog A W (Additive.ofMul u) =
      infinitePlaceLog W (Additive.ofMul
        (sourceFmodUnitsToInfiniteCompletion A W u)) := rfl

end C2Infinite

end LeanFormal.IUT.XiFPaper.S3139C2InfiniteCompletionUnitsActual

end
