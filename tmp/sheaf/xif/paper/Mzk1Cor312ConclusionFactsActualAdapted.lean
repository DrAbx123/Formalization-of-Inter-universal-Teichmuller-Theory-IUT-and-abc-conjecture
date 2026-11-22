import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract

/-! Mainline: Cor312Conclusion unfolding and ordered-chain facts (real proofs). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312ConclusionFactsActualAdapted

open LeanFormal.IUT

theorem cor312Conclusion_iff (C : StepXIContract) :
    Cor312Conclusion C ↔ C.qSigned ≤ C.thetaSigned :=
  Iff.rfl

theorem cor312Conclusion_ordered (C : StepXIContract) :
    C.qSigned ≤ C.targetSigned ∧ C.targetSigned ≤ C.thetaSigned :=
  ⟨C.q_le_target, C.target_le_theta⟩

theorem contract_q_negative (C : StepXIContract) : C.qSigned < 0 :=
  C.q_negative

theorem contract_conclusion_of_ordered (C : StepXIContract) :
    Cor312Conclusion C :=
  cor312_of_constructed_stepXI C

end LeanFormal.IUT.XiFPaper.Mzk1Cor312ConclusionFactsActualAdapted