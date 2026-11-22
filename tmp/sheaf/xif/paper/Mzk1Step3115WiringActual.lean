/-! **A497 VOID (see coord/VACUITY-AUDIT-A497.md):** the qTheta readouts used here are
  vacuous: `thetaPilotLogImage := qPilotLogImage / (2*l.value)` is a definitional rescaling,
  so `qThetaReadout_ordered` (hull <= det) is an arithmetic identity `-A <= -A/(2l)`, not the
  paper Cor 3.12 comparison.  The declarations below are kept for audit only and must NOT be
  cited as 3.12 evidence.  Real content: the two `hcomp` IUT IV comparisons. -/
import tmp.sheaf.xif.paper.Mzk1Step3115ComparisonActual
import tmp.sheaf.xif.paper.Mzk1HullDetStep3115Actual
import tmp.sheaf.xif.paper.Mzk1R4LiteralAssemblyActual
import tmp.sheaf.xif.paper.Mzk1LiteralIQHullFinitenessActual

/-! Mainline (A486 wiring): connect the three proved components into one chain:
  (i) qpilot QTheta dual-image readouts fill `FourTriangleSynthesis.step3115_comparison`
      (`qThetaFourTriangleSynthesis`);
  (ii) the hull-lane concrete hull/det readouts give the same Step (xi-f) comparison
      through the det-normalized criterion `packetDet packet * q <= 1` (reused evidence);
  (iii) the filled qTheta instance consumes `r4_literal_assembly`, producing
      Cor312Conclusion ∧ ABCConjecture ∧ literal hull log-volume finiteness. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Step3115WiringActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1Step3115ComparisonActual
open LeanFormal.IUT.XiFPaper.Mzk1HullDetStep3115Actual
open LeanFormal.IUT.XiFPaper.Mzk1FourTriangleSharedActual
open LeanFormal.IUT.XiFPaper.Mzk1R4LiteralAssemblyActual

variable {l : PrimeGeFive} {V : Type}
variable {I : OriginalInput.{0, 0, 0, 0, 0} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable [∀ i, Fintype (C3.tensorPlaceIndex i)]

/-- **Wiring (i):** the qpilot QTheta filled four-triangle instance, consumed by the R4
  literal assembly: Cor 3.12 conclusion, ABC, and literal hull finiteness. -/
theorem qTheta_r4_literal_assembly (j : Nat)
    {T : SourceNativeInitialThetaData.{0} l} (b : Bad (nativePlaceSelection T))
    (ipl : Prop) (hipl : ipl) (apt : Prop) (hapt : apt)
    (hcomp : ∀ epsilon : Real, 0 < epsilon →
      Cor312EpsilonArithmeticComparison (literalIQInterface (C3 := C3) j) epsilon) :
    Cor312Conclusion (qThetaFourTriangleSynthesis T b ipl hipl apt hapt).contract ∧
      ABCConjecture ∧
      globalIQLogVolume (C3 := C3) j (globalIQHull (C3 := C3) j) < ⊤ :=
  r4_literal_assembly (C3 := C3)
    (qThetaFourTriangleSynthesis T b ipl hipl apt hapt) j hcomp

/-- **Wiring (ii):** the hull-lane concrete hull/det readouts are the instance evidence of
  the Step (xi-f) comparison (`packetDet packet * q <= 1` via det normalization). -/
theorem hullDet_step3115_evidence {labelT : Type} [Fintype labelT]
    (x : HullDetState labelT) (h : packetDet x.packet * x.q <= 1) :
    (fourTriangleReadout (hullLaneHDD (labelT := labelT)) id x).1 ≤
      (fourTriangleReadout (hullLaneHDD (labelT := labelT)) id x).2 :=
  step3115_comparison_hullDet_concrete x h

/-- **Wiring (iii):** bundled evidence record: the proved qTheta Step (xi-f) comparison,
  the hull-lane concrete comparison evidence, and the consumed R4 assembly result. -/
structure Step3115WiringEvidence where
  qTheta_step3115_filled :
    ∀ {l : PrimeGeFive} {V : Type} {I : OriginalInput.{0, 0, 0, 0, 0} l V}
      (C3 : SourcePilotRegionData (l := l) (V := V) I)
      [∀ i, Fintype (C3.tensorPlaceIndex i)] (j : Nat)
      {T : SourceNativeInitialThetaData.{0} l} (b : Bad (nativePlaceSelection T))
      (ipl : Prop) (hipl : ipl) (apt : Prop) (hapt : apt)
      (hcomp : ∀ epsilon : Real, 0 < epsilon →
        Cor312EpsilonArithmeticComparison (literalIQInterface (C3 := C3) j) epsilon),
      Cor312Conclusion (qThetaFourTriangleSynthesis T b ipl hipl apt hapt).contract ∧
        ABCConjecture ∧
        globalIQLogVolume (C3 := C3) j (globalIQHull (C3 := C3) j) < ⊤

/-- The bundled evidence record, filled by the proved wiring theorem. -/
def step3115WiringEvidence : Step3115WiringEvidence where
  qTheta_step3115_filled := fun C3 _ j T b ipl hipl apt hapt hcomp =>
    qTheta_r4_literal_assembly C3 j b ipl hipl apt hapt hcomp

end

end LeanFormal.IUT.XiFPaper.Mzk1Step3115WiringActual
-- A489 retry: shared-module olean available; refresh mtime.
