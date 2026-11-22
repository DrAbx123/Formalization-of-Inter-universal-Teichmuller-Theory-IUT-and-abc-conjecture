import LeanFormal.IUT.Audit.Status

/-! # S3149: net residual classification (after A23)

Which residuals remain genuinely external/ABC-strength after the B/C
reclassifications.  No sorry/axiom. -/

namespace LeanFormal.IUT.Audit

/-- (residual area, class after A23, note) rows. -/
def S3149NetResidualClasses : List (String × String × String) := [
  ("R1.M1 / R1.M2b", "B/C contract/convention", "dischargeable by from-scratch model (A23); not external"),
  ("F4.a", "B elementary identification", "faithfulness proved; elementary identification target"),
  ("F4.b", "contract data + elementary lemma", "unit-log-zero elementary; not a paper hypothesis"),
  ("F4.c.cardP", "ABC-strength", "ABCHeightWeightAdditiveBoundV2 remains the single ABC-strength residual"),
  ("LGP.residuals", "component residuals", "stage4 wiring; classes per its ledger"),
  ("ThetaHalf residuals", "hull-owned", "C3-side readout; independent handoff, not gate hypothesis") ]

theorem S3149NetResidualClasses_length : S3149NetResidualClasses.length = 6 := rfl

/-- Net-classification record. -/
def S3149NetClassification : Obligation :=
  { id := "IUT.project.net-residual-classification-a23"
    source := "A23 reclassification; registry 13129; acceptance record appendices"
    status := VerificationStatus.interface
    note :=
      "NET AFTER A23: no NEW genuine D-class external input for M1/M2b/F4.a/F4.b (they are B/C "
      ++ "contract/convention, dischargeable by the from-scratch model); F4.c.cardP remains the "
      ++ "single ABC-strength residual (ABCHeightWeightAdditiveBoundV2); ThetaHalf is hull-owned "
      ++ "independent handoff, not a gate hypothesis. Pins unchanged; doc-only update."
    dependsOn := [ "S3149CitationA23Reclassification" ] }

#check S3149NetClassification
#check S3149NetResidualClasses_length

end LeanFormal.IUT.Audit
