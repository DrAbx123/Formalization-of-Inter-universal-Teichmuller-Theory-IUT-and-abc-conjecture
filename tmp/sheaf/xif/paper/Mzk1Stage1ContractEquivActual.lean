import tmp.sheaf.xif.paper.Mzk1Signed312AssemblyActual
import tmp.sheaf.xif.paper.Mzk1XiFFormalStepActual
import tmp.sheaf.xif.paper.RefGogopexRealLineCopyActual
import tmp.sheaf.xif.paper.RefGogopexPilotComparisonActual

/-! # Stage-1 / contract equivalence for signed 3.12 (no vacuous target) -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage1ContractEquivActual

open Iut Iut.Stage1 LeanFormal.IUT

/-- Signed 3.12 inequality for a contract is exactly its comparison chain. -/
theorem corollary312Inequality_iff_contract (C : StepXIContract) :
    Corollary312Inequality
      ⟨PilotSide.theta, -C.thetaSigned⟩
      ⟨PilotSide.q, -C.qSigned⟩ ↔ C.qSigned ≤ C.thetaSigned := by
  unfold Corollary312Inequality
  constructor · intro h; linarith · intro h; linarith

/-- Positive transport preserves the signed 3.12 inequality of pilot volumes. -/
theorem transport_preserves_signed312 {source target : RealLineCopy.Copy}
    (f : RealLineCopy.Transport source target) {theta q : Real}
    (h : q ≤ theta) :
    -(f.scale.val * theta) ≤ -(f.scale.val * q) := by
  have hnonneg : (0 : Real) ≤ f.scale.val := le_of_lt f.scale.pos
  have hmul : f.scale.val * q ≤ f.scale.val * theta :=
    mul_le_mul_of_nonneg_left h hnonneg
  linarith

/-- A contract comparison gives the Stage-1 signed inequality after positive transport. -/
theorem stage1_signed312_of_contract {source target : RealLineCopy.Copy}
    (f : RealLineCopy.Transport source target) (C : StepXIContract) :
    -(f.scale.val * C.thetaSigned) ≤ -(f.scale.val * C.qSigned) :=
  transport_preserves_signed312 f (le_trans C.q_le_target C.target_le_theta)

end LeanFormal.IUT.XiFPaper.Mzk1Stage1ContractEquivActual
