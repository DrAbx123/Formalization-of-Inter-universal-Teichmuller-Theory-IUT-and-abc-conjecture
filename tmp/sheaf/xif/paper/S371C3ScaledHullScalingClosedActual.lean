import tmp.sheaf.xif.paper.S353C3LatticeScaledHullActual

/-!
# S371: scaled-hull invariance under base Z_p-unit scaling

Uses the actual unit-region scaling invariance from S353 and the fact that the
Q_p scaling scalar commutes with the base Z_p scalar action.
-/

noncomputable section
open scoped BigOperators Pointwise
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S371C3ScaledHullScalingClosedActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S349C3TensorLatticeRegionActual
open LeanFormal.IUT.XiFPaper.S353C3LatticeScaledHullActual
open MeasureTheory

variable {l : PrimeGeFive} {V : Type}
variable {I : OriginalInput.{0, 0, 0, 0, 0} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- The Q_p-scaled corrected lattice region is invariant under base Z_p-unit
scaling. -/
theorem literalScaledRegion_scalingClosed
    (a : ℚ_[C3.p]) :
    BaseZPUnitScalingClosed C3 (literalScaledRegion C3 a) := by
  intro z
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    rw [literalScaledRegion, Set.mem_smul_set] at hy ⊢
    rcases hy with ⟨o, ho, rfl⟩
    refine ⟨z • o, ?_, ?_⟩
    · exact (actualC3LogShellTensorLattice C3).smul_mem (z : ℤ_[C3.p]) ho
    · rw [← hxy]
      change a • ((z : ℤ_[C3.p]) • o) =
        (z : ℤ_[C3.p]) • (a • o)
      exact smul_comm a (z : ℤ_[C3.p]) o
  · intro hx
    rw [literalScaledRegion, Set.mem_smul_set] at hx
    rcases hx with ⟨o, ho, hxo⟩
    rw [← hxo]
    refine ⟨a • ((↑(z⁻¹) : ℤ_[C3.p]) • o), ?_, ?_⟩
    · rw [literalScaledRegion, Set.mem_smul_set]
      exact ⟨(↑(z⁻¹) : ℤ_[C3.p]) • o,
        (actualC3LogShellTensorLattice C3).smul_mem (↑(z⁻¹) : ℤ_[C3.p]) ho, rfl⟩
    · calc
        (fun x : C3LogShellTensorBlock C3 => (z : ℤ_[C3.p]) • x)
            (a • ((↑(z⁻¹) : ℤ_[C3.p]) • o))
            = a • ((z : ℤ_[C3.p]) • ((↑(z⁻¹) : ℤ_[C3.p]) • o)) := by
              change (z : ℤ_[C3.p]) • (a • ((↑(z⁻¹) : ℤ_[C3.p]) • o)) =
                a • ((z : ℤ_[C3.p]) • ((↑(z⁻¹) : ℤ_[C3.p]) • o))
              exact (smul_comm a (z : ℤ_[C3.p]) _).symm
        _ = a • (((z : ℤ_[C3.p]) * (↑(z⁻¹) : ℤ_[C3.p])) • o) := by
              rw [smul_smul]
        _ = a • o := by simp

/-- The literal scaled hull is invariant under base Z_p-unit scaling. -/
theorem literalHull_scalingClosed
    (a : ℚ_[C3.p]) (ha : a ≠ 0) :
    BaseZPUnitScalingClosed C3
      (literalHull C3 (literalScaledRegion C3 a)) := by
  rw [literalHull_eq_scaledRegion C3 a ha]
  exact literalScaledRegion_scalingClosed C3 a

/-- The former S353 gap is inhabited. -/
theorem literalScaledHullScalingClosedGap_holds
    (a : ℚ_[C3.p]) (ha : a ≠ 0) :
    literalScaledHullScalingClosedGap C3 a ha :=
  literalHull_scalingClosed C3 a ha

end LeanFormal.IUT.XiFPaper.S371C3ScaledHullScalingClosedActual

end
