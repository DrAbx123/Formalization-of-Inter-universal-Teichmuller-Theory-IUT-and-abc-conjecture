/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ProductHaarSingletonActual
import tmp.sheaf.xif.paper.Mzk1ScalingDirectionActual
import tmp.sheaf.xif.paper.Mzk1BadPartActual
import tmp.sheaf.xif.paper.Mzk1GapShapeAuditActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.PaperRootExtensionProductHaarActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual

/-! # A688 hull: FINAL BOUNDARY SEMANTICS — three-state status audit

Canonical final semantics (A688, aligned with `Mzk1FinalBoundaryCertificateV2Actual`):

1. Cor 3.12 requirement chain: GREEN;
2. corrected-region **Gap 1 is a THEOREM** (explicit full bad support, `d_b ≥ 1`,
   `unit ≥ 0`) — mainline `Mzk1CorrectedGap1UnconditionalActual`;
3. corrected **Gap 2 shape ⇒ ABC is a THEOREM** (mainline
   `Mzk1CorrectedGap2ToABCActual` / `finalBoundaryCertificateV2`);
4. the ONLY remaining named input is the corrected-region Gap 2 shape; it is
   equivalent (`correctedGap2_iff_arith`, mainline) to the pure arithmetic
   `BadSumWeightBound`: `Σ_b e_b d_b log p_b ≤ (1+ε)·arithmeticWeight + D'`;
5. the converse (ABC ⇒ Gap 2) is NOT proved and NOT claimed;
6. ABC gate NOT passed; no canonical object changed.

Misleading name `corrected_gap2_iff_ABC` is NOT used here (only the θ-absorption
equivalence exception is allowed elsewhere).  This file is statement-only and
records the three states (PROVED-CHAIN / NAMED / NOT-PROVED) explicitly. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1HullFinalSemanticsAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.Mzk1ProductHaarSingletonActual
open LeanFormal.IUT.XiFPaper.Mzk1ScalingDirectionActual
open LeanFormal.IUT.XiFPaper.Mzk1BadPartActual
open LeanFormal.IUT.XiFPaper.Mzk1GapShapeAuditActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [Nonempty (Bad (nativePlaceSelection T))]

/-- Canonical final-boundary status table (three states). -/
def finalSemanticsRows : List (String × String × String) :=
  [ ("Cor 3.12 requirement chain", "resolved requirement + strict_measure", "PROVED-CHAIN (GREEN)"),
    ("corrected-region Gap 1", "Mzk1CorrectedGap1UnconditionalActual", "PROVED-CHAIN (THEOREM; explicit full support/d_b≥1/unit≥0)"),
    ("corrected Gap 2 shape ⇒ ABC", "correctedGap2_to_ABC / finalBoundaryCertificateV2", "PROVED-CHAIN (THEOREM)"),
    ("corrected-region Gap 2 shape", "corrected Gap2 shape", "NAMED (only remaining input)"),
    ("corrected Gap2 ⇔ BadSumWeightBound", "correctedGap2_iff_arith", "PROVED-CHAIN (pure arithmetic reduction)"),
    ("ABC ⇒ corrected Gap 2", "converse", "NOT-PROVED / NOT CLAIMED"),
    ("ABC gate", "final boundary", "NOT PASSED; no canonical change") ]

theorem finalSemanticsRows_length : finalSemanticsRows.length = 7 := rfl

/-- Hull evidence row (B1): point-supported regions have zero product Haar. -/
theorem hull_b1_evidence (x : RootExtensionProductCarrier T) :
    rootExtensionProductHaar T ({x} : Set (RootExtensionProductCarrier T)) = 0 :=
  productHaar_singleton_zero T x

/-- Hull evidence row (inverse scaling): the bad-support product measure law. -/
theorem hull_scaling_evidence {N : Nat} (hN : 0 < N)
    (S : (b : Bad (nativePlaceSelection T)) → Set (rootNormedExtension T b)) :
    rootExtensionProductHaar T (badInvScale T hN '' Set.pi Set.univ S) =
      (∏ b : Bad (nativePlaceSelection T), localInvFactor T hN b) *
        rootExtensionProductHaar T (Set.pi Set.univ S) :=
  badInvScale_measure T hN S

/-- Hull evidence row (corrected `N_bad`): `badPart N ∣ N` and `≤ N`. -/
theorem hull_badPart_evidence {N : Nat} (hN : 0 < N) :
    badPart T N ∣ N ∧ badPart T N ≤ N :=
  ⟨badPart_dvd T hN, badPart_le T hN⟩

#print axioms LeanFormal.IUT.XiFPaper.Mzk1HullFinalSemanticsAuditActual.hull_b1_evidence
#print axioms LeanFormal.IUT.XiFPaper.Mzk1HullFinalSemanticsAuditActual.hull_scaling_evidence
#print axioms LeanFormal.IUT.XiFPaper.Mzk1HullFinalSemanticsAuditActual.hull_badPart_evidence

end LeanFormal.IUT.XiFPaper.Mzk1HullFinalSemanticsAuditActual

end