import tmp.sheaf.xif.paper.S77CompletionIntegersEquivActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedIntegers

/-! # S79: actual integral-ring equivalence via normalized unit-ball theorem

FinitePlaceNormalizedIntegers proves that the normalized spectral unit ball and
the adic completion integers have the same elements, via the continuous
normalizedCompletionRingEquiv.  This closes the S77 carrier hypothesis.

No fake equality/sorry/axiom/True/PUnit. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S79IntegralRingEquivActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.XiFPaper.S77CompletionIntegersEquivActual

universe u

variable {K : Type u} [Field K] [NumberField K]
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime K p)

/-- Actual carrier equality proved from the normalized unit-ball theorem. -/
theorem completionIntegersCarrierEq_holds :
    completionIntegersCarrierEq (K := K) (p := p) place := by
  intro x
  constructor
  · intro hx
    rw [mem_integers_iff]
    exact (normalizedCompletion_norm_le_one_iff place.val x).mp
      ((mem_completionIntegers_iff_norm_le_one place.val
        (x : Completion place.val)).mp hx)
  · intro hx
    have hxnorm : ‖x‖ ≤ 1 := (mem_integers_iff x).mp hx
    exact (mem_completionIntegers_iff_norm_le_one place.val
      (x : Completion place.val)).mpr
      ((normalizedCompletion_norm_le_one_iff place.val x).mpr hxnorm)

/-- Actual ring equivalence CompletionIntegers place -> Integers completion. -/
noncomputable def completionIntegersEquivIntegers :
    (CompletionIntegers place.val : Type u) ≃+*
      Integers (CommonPrimeCompletion place) :=
  completionIntegersRingEquivOfCarrierEq (K := K) (p := p) place
    (completionIntegersCarrierEq_holds (K := K) (p := p) place)

/-- The actual equivalence is the identity on underlying completion elements. -/
theorem completionIntegersEquivIntegers_coe
    (x : (CompletionIntegers place.val : Type u)) :
    ((completionIntegersEquivIntegers (K := K) (p := p) place x :
      Integers (CommonPrimeCompletion place)) : CommonPrimeCompletion place) =
      x.1 := rfl

end LeanFormal.IUT.XiFPaper.S79IntegralRingEquivActual

end
