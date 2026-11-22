import tmp.sheaf.xif.paper.Mzk1Gap2ArithmeticReductionActual
import tmp.sheaf.xif.paper.Mzk1FinalBoundaryCertificateV2Actual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# stepxi corrected Gap2 semantics (A688)

Correct final semantics:
* corrected Gap2 shape ⇔ pure arithmetic `BadSumWeightBound` (PROVED);
* corrected Gap2 shape ⇒ ABC (PROVED, via the final boundary V2);
* ABC ⇒ corrected Gap2 is NOT proved/asserted.
No `corrected_gap2_iff_ABC` claim. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXICorrectedGap2SemanticsActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1Gap2ArithmeticReductionActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

theorem correctedGap2_arith_equiv
    (point : Nat → Nat → Nat → S1902Carrier T)
    (eN : Nat → Nat → Nat → Bad (nativePlaceSelection T) → Nat)
    (hc0 : s1902HaarScale T ≠ 0) (hcT : s1902HaarScale T < ⊤)
    (hhull : 0 ≤ (s1902LogVolume T (s1902Hull T)).toReal) :
    CorrectedGap2Shape T point eN ↔ BadSumWeightBound T eN :=
  correctedGap2_iff_arith T point eN hc0 hcT hhull

#print axioms LeanFormal.IUT.XiFPaper.Mzk1Gap2ArithmeticReductionActual.correctedGap2_iff_arith
#print axioms LeanFormal.IUT.XiFPaper.Mzk1FinalBoundaryCertificateV2Actual.finalBoundaryCertificateV2

end LeanFormal.IUT.XiFPaper.Mzk1StepXICorrectedGap2SemanticsActual

end
