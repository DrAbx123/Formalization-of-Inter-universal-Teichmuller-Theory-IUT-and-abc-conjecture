import tmp.sheaf.xif.paper.RefGogopexPilotComparisonActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract

/-! # Signed 3.12 assembly: StepXIContract to Gogopex Stage1Comparison -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Signed312AssemblyActual

open Iut.Stage1 LeanFormal.IUT

/-- The Stage-1 comparison package associated to a StepXI contract. -/
def stage1ComparisonOfContract (C : StepXIContract) : Stage1Comparison where
  theta := ⟨PilotSide.theta, -C.thetaSigned⟩
  q := ⟨PilotSide.q, -C.qSigned⟩
  theta_side := rfl
  q_side := rfl
  q_positive := neg_pos.mpr C.q_negative
  comparison := by
    unfold Corollary312Inequality
    have h : C.qSigned ≤ C.thetaSigned := le_trans C.q_le_target C.target_le_theta
    linarith

/-- The contract comparison is exactly the signed inequality of Cor 3.12. -/
theorem corollary312Inequality_of_contract (C : StepXIContract) :
    -C.thetaSigned ≤ -C.qSigned := by
  have h : C.qSigned ≤ C.thetaSigned := le_trans C.q_le_target C.target_le_theta
  linarith

/-- Conversely, a signed Cor 3.12 inequality is a contract-shaped comparison. -/
theorem contract_comparison_of_signedInequality {thetaSigned qSigned : Real}
    (h : -thetaSigned ≤ -qSigned) : qSigned ≤ thetaSigned := by
  linarith

end LeanFormal.IUT.XiFPaper.Mzk1Signed312AssemblyActual
