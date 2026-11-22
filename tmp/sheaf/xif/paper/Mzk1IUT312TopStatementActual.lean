import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract

/-!
  Mainline: precise top-statement layer for paper IUT III Corollary 3.12 at the
  Step-XI contract boundary.  The contract construction itself remains unfinished
  (tree audit note); these declarations are real consequences only.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1IUT312TopStatementActual

open LeanFormal.IUT

/-- IUT 3.12 top statement at contract level: a Step-XI contract exists whose
  ordered q <= theta conclusion holds. -/
def IUT312TopStatement : Prop :=
  ∃ C : StepXIContract, Cor312Conclusion C

/-- Any supplied contract yields the top statement (contract conclusion is proved). -/
theorem iut312TopStatement_of_contract (C : StepXIContract) :
    IUT312TopStatement :=
  ⟨C, cor312_of_constructed_stepXI C⟩

/-- Definitional unfolding of the top statement. -/
theorem iut312TopStatement_iff :
    IUT312TopStatement ↔ ∃ C : StepXIContract, C.qSigned ≤ C.thetaSigned :=
  Iff.rfl

/-- q-pilot positivity from any contract. -/
theorem iut312_qPositive_of_contract (C : StepXIContract) :
    0 < -C.qSigned :=
  q_positive_of_constructed_stepXI C

/-- The conclusion shape (paper: q < 0 and q <= theta). -/
def IUT312ConclusionShape : Prop :=
  ∃ q theta : ℝ, q < 0 ∧ q ≤ theta

theorem iut312ConclusionShape_of_top (h : IUT312TopStatement) :
    IUT312ConclusionShape := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C.qSigned, C.thetaSigned, C.q_negative, hC⟩

end LeanFormal.IUT.XiFPaper.Mzk1IUT312TopStatementActual