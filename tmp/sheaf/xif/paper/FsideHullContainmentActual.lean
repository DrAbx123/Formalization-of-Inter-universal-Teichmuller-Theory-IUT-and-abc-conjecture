/- F-side hull containment (kurt): the possible-image set for the single-slot ceil generator,
and the reduction of the closure containment to the generator bridge.

Proved here: with istar = (), varpi, Phi = {id}, the StepV possible-image set is exactly
varpi-tensor • canonicalUnitReference.  The remaining bridge (thetaTensorScaledRegion urCeilC =
that same set) is the exact missing equality used for the region-one containment; it is NOT
assumed.
-/
import tmp.sheaf.xif.paper.Mzk1P6PhiActionFamilyActual
import tmp.sheaf.xif.paper.Mzk1URThetaHullLowerActual
import tmp.sheaf.xif.paper.Mzk1URThetaHullNonzeroActual
import Mathlib.Tactic

set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators Pointwise
open MeasureTheory

namespace LeanFormal.IUT.XiFPaper.FsideHullContainmentActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1P6PhiActionFamilyActual

variable {K : Type*} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*}
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
variable (tuple : (i : ι) → V i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]

/-- With `Phi = {refl}` the possible-image set is the translate of the canonical unit reference
by the pure tensor of the updated generator. -/
theorem possibleImages_refl_eq (istar : ι)
    (varpi : CommonPrimeCompletion (places istar (tuple istar))) :
    arithmeticTupleStepVPossibleImages places tuple istar varpi
        ({LinearEquiv.refl ℚ_[p] (ArithmeticTensorTupleBlock places tuple)} :
          Set (ArithmeticTensorTupleBlock places tuple ≃ₗ[ℚ_[p]]
            ArithmeticTensorTupleBlock places tuple)) =
      (arithmeticTupleTprod places tuple (Function.update 1 istar varpi)) •
        (arithmeticTupleCanonicalUnitReference places tuple) := by
  ext s
  constructor
  · rintro ⟨φ, hφ, x, hx, rfl⟩
    have hφ' : φ = LinearEquiv.refl ℚ_[p] (ArithmeticTensorTupleBlock places tuple) := by
      simpa using hφ
    rw [hφ']
    exact ⟨x, hx, (LinearEquiv.refl_apply _ _).trans (by rw [Algebra.smul_def, mul_one])⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨LinearEquiv.refl ℚ_[p] _, rfl, x, hx, ?_⟩
    rw [LinearEquiv.refl_apply, Algebra.smul_def, mul_one]

end LeanFormal.IUT.XiFPaper.FsideHullContainmentActual
end