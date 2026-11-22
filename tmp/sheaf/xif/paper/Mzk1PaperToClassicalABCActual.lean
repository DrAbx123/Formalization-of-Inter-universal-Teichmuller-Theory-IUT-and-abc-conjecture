import tmp.sheaf.xif.paper.Mzk1ClassicalABCToOurABCActual
import tmp.sheaf.xif.paper.Mzk1N3SharedContainerBridgeShaActual
import tmp.sheaf.xif.paper.Mzk1Paper312ConclusionRealActual
import tmp.sheaf.xif.paper.Mzk1ScaledClosingShaActual
import tmp.sheaf.xif.paper.Mzk1ScaledPaper312Actual
import Mathlib.Tactic

/-!
# A905 audit + partial assembly: our paper chain -> ClassicalABCShape

Objects:
* `ScaledPaper312Statement T qReading k` (`Mzk1ScaledPaper312Actual:58`)
  := `qReading ≤ thetaScaledLog T k`;
* `paperGap D` (`Mzk1N3SharedContainerRealActual:109`)
  := `D.qPilotVolumeReading ≤ D.thetaPilotVolumeReading`;
* `Paper312Statement C3 P` (S3137 real readings) := `qThetaPilotLogVolumeComparison`;
* `Cor312Conclusion C` (`IUTIII/.../StepXI/Contract.lean`) := `C.qSigned ≤ C.targetSigned`
  (`Mzk1SignedCor312ContractActual.signedCor312_conclusion` constructs it);
* `ClassicalABCShape` (`Mzk1ClassicalABCToOurABCActual:21`) := lana `Iut.ClassicalABC` shape.

Green edges (proved, oleans present):
1. `paperGap D ↔ Paper312Statement C3 P` — `paperGap_iff_paper312Statement`;
2. `Paper312Statement + qneg + IPL/SHE/APT ⇒ Cor312Conclusion` — `cor312_of_sharedPaperGap`;
3. `ScaledPaper312Statement ↔ VPaper ≥ 0` — `scaledPaper312_iff_VPaper_nonneg`;
4. `ScaledPaper312Statement ↔ qSideContribution ≥ 1 - scaledClosedFormR` —
   `scaledPaper312_iff_closedForm`;
5. `ClassicalABCShape ⇒ ABCConjecture` — `abcConjecture_of_classicalABCShape`.

Missing edges (exact names):
* **`paperGap_to_scaledPaper312`**: no theorem linking `paperGap D` (real C3 readings)
  to `ScaledPaper312Statement T qReading k` (scaled θ-hull normalized log).  The
  missing identity is `thetaPilotHullLogVolumeReal C3 = thetaScaledLog T k` (or the
  corresponding closed-form comparison) for the chosen `k` — an analytic identification;
* **`scaledPaper312_to_ssIneqExplicit`** / **`VPaper_to_ssIneq`**: `ScaledPaper312Statement`
  gives `VPaper ≥ 0` and `qSideContribution ≥ 1 - scaledClosedFormR`, but the SSIneq
  coefficient dictionary `(sFactor(nC)-1)A ≤ V_paper` (procession/archimedean/c_lana)
  is PENDING (see `Mzk1ScaledClosingShaActual.closingRows`, row `remaining SSIneq
  coefficient dictionary`);
* **`cor312Conclusion_to_classicalABCShape`**: no theorem from `Cor312Conclusion C`
  to `ClassicalABCShape` (or to `Iut.Cor312VariantHolds`); the only conditional ABC
  consumers use `Iut.WallEquiv.classicalABC_of_ss` (lana oleans absent;
  `Mzk1SSIneqConsumerChainActual` cannot compile) or the ABCBridge named-input
  interface (`Mzk1Cor312ToABCConsumerActual`), not `Cor312Conclusion`;
* **`ssIneq_to_classicalABCShape`**: the lana consumer `Iut.WallEquiv.classicalABC_of_ss`
  is the missing external edge; once its olean exists, `SSIneq → ClassicalABCShape`
  needs the dictionary between `Iut.ClassicalABC` and our `ClassicalABCShape`
  (currently only `ClassicalABCShape → ABCConjecture` is proved).

Verdict: the chain is **not complete**.  Green part: scaled ↔ VPaper/closed form,
paperGap ↔ Paper312Statement, ⇒ Cor312Conclusion, ClassicalABCShape ⇒ ABC.  Missing:
paperGap ↔ scaled, scaled/VPaper ⇒ SSIneq, Cor312Conclusion/SSIneq ⇒ ClassicalABCShape.
No fake assembly and no RETRACTED statement.  No sorry/axiom/True.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1PaperToClassicalABCActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.Mzk1ClassicalABCToOurABCActual
open LeanFormal.IUT.XiFPaper.Mzk1N3SharedContainerRealActual
open LeanFormal.IUT.XiFPaper.Mzk1N3SharedContainerBridgeShaActual
open LeanFormal.IUT.XiFPaper.Mzk1Paper312ConclusionRealActual
open LeanFormal.IUT.XiFPaper.Mzk1ScaledPaper312Actual
open LeanFormal.IUT.XiFPaper.Mzk1ScaledClosingShaActual
open LeanFormal.IUT.XiFPaper.Mzk1SignedCor312ContractActual
open LeanFormal.IUT.XiFPaper.Mzk1VPaperActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open scoped BigOperators ENNReal

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PaperQPilotObjectActual (l := l) (I := I))
variable (D : SharedContainerReal C3 P)

/-- Green edge 1 re-export: `paperGap ↔ Paper312Statement`. -/
theorem paperGap_iff_paper312Statement' :
    paperGap D ↔ Mzk1Paper312StatementActual.Paper312Statement C3 P :=
  paperGap_iff_paper312Statement C3 P D

/-- Green edge 2 re-export: paperGap + q-negativity + qualitative evidence ⇒ Cor312Conclusion. -/
theorem paperGap_to_cor312Conclusion (hcmp : paperGap D)
    (hqneg : qPilotLogVolumeReading P < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (signedCor312Contract (qPilotLogVolumeReading P)
        (thetaPilotHullLogVolumeReal C3) hqneg ipl hipl she hshe apt hapt
        (by simpa [qThetaPilotLogVolumeComparison] using
          (paperGap_iff_qThetaComparison C3 P D).mp hcmp)) :=
  cor312_of_sharedPaperGap C3 P D hcmp hqneg ipl hipl she hshe apt hapt

/-- Green edge 5 re-export: `ClassicalABCShape ⇒ ABCConjecture`. -/
theorem classicalABCShape_to_ABCConjecture (h : ClassicalABCShape) :
    ABCConjecture :=
  abcConjecture_of_classicalABCShape h

/-- Missing edge 1 (named): `paperGap ↔ ScaledPaper312Statement` for the chosen `k`.
Not provided by any green theorem; it is the analytic identification of
`thetaPilotHullLogVolumeReal` with `thetaScaledLog T k` (or the closed-form comparison). -/
def MissingEdge_paperGap_to_scaledPaper312 : String :=
  "thetaPilotHullLogVolumeReal C3 = thetaScaledLog T k (or paperGap <-> ScaledPaper312Statement)"

/-- Missing edge 2 (named): `ScaledPaper312Statement` (or `VPaper ≥ 0`) ⇒ `SSIneqExplicit`;
the blocker is the procession/archimedean/c_lana coefficient dictionary. -/
def MissingEdge_scaledPaper312_to_ssIneqExplicit : String :=
  "(sFactor(nC)-1)*A <= V_paper coefficient dictionary (procession/arch/c_lana) PENDING"

/-- Missing edge 3 (named): `Cor312Conclusion ⇒ ClassicalABCShape`. -/
def MissingEdge_cor312Conclusion_to_classicalABCShape : String :=
  "no theorem from Cor312Conclusion C to ClassicalABCShape / Iut.Cor312VariantHolds"

/-- Missing edge 4 (named): `SSIneq ⇒ ClassicalABCShape`; needs lana
`Iut.WallEquiv.classicalABC_of_ss` olean plus the ClassicalABC dictionary. -/
def MissingEdge_ssIneq_to_classicalABCShape : String :=
  "Iut.WallEquiv.classicalABC_of_ss (olean absent) + ClassicalABC -> ClassicalABCShape dictionary"

structure EdgeRow where
  edge : String
  theoremName : String
  status : String
  deriving Repr, DecidableEq

def edgeRows : List EdgeRow :=
  [ ⟨"ScaledPaper312Statement <-> VPaper >= 0", "Mzk1VPaperActual.scaledPaper312_iff_VPaper_nonneg", "GREEN"⟩
  , ⟨"ScaledPaper312Statement <-> qSide >= 1 - scaledClosedFormR", "Mzk1ScaledClosingShaActual.scaledPaper312_iff_closedForm", "GREEN"⟩
  , ⟨"paperGap <-> Paper312Statement", "Mzk1N3SharedContainerBridgeShaActual.paperGap_iff_paper312Statement", "GREEN"⟩
  , ⟨"paperGap + qneg + IPL/SHE/APT => Cor312Conclusion", "cor312_of_sharedPaperGap", "GREEN"⟩
  , ⟨"ClassicalABCShape => ABCConjecture", "Mzk1ClassicalABCToOurABCActual.abcConjecture_of_classicalABCShape", "GREEN"⟩
  , ⟨"paperGap <-> ScaledPaper312Statement", "MissingEdge_paperGap_to_scaledPaper312", "PENDING"⟩
  , ⟨"ScaledPaper312Statement/VPaper => SSIneqExplicit", "MissingEdge_scaledPaper312_to_ssIneqExplicit", "PENDING"⟩
  , ⟨"Cor312Conclusion => ClassicalABCShape", "MissingEdge_cor312Conclusion_to_classicalABCShape", "PENDING"⟩
  , ⟨"SSIneq => ClassicalABCShape", "MissingEdge_ssIneq_to_classicalABCShape", "PENDING"⟩
  , ⟨"scope", "audit + green partial assembly only; no fake ABC", "INTEGRITY"⟩
  ]

theorem edgeRows_length : edgeRows.length = 10 := rfl

theorem edgeRows_has_pending :
    edgeRows.any (fun r => r.status = "PENDING") = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1PaperToClassicalABCActual

#print axioms LeanFormal.IUT.XiFPaper.Mzk1PaperToClassicalABCActual.paperGap_iff_paper312Statement'
#print axioms LeanFormal.IUT.XiFPaper.Mzk1PaperToClassicalABCActual.paperGap_to_cor312Conclusion
#print axioms LeanFormal.IUT.XiFPaper.Mzk1PaperToClassicalABCActual.classicalABCShape_to_ABCConjecture
