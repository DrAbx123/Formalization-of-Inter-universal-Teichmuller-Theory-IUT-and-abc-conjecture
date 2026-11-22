import tmp.sheaf.xif.paper.S2605LiftSLActual

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace LeanFormal.IUT.XiFPaper.S2606SmulEqMulActual

open LeanFormal.IUT.XiFPaper.S2605LiftSLActual

lemma smul_eq_mul (c : Cb) (s : Sb) : c • s = algebraMap Cb Sb c * s := by
  induction s using Localization.induction_on with
  | H y =>
    rcases y with ⟨a, b⟩
    simp [Localization.mk_eq_mk', Algebra.smul_def]


end LeanFormal.IUT.XiFPaper.S2606SmulEqMulActual
end