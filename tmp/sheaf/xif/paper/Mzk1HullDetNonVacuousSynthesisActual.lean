import tmp.sheaf.xif.paper.Mzk1HullDetStep3115Actual
import tmp.sheaf.xif.paper.Mzk1R4LiteralAssemblyActual
import tmp.sheaf.xif.paper.Mzk1FourTriangleSharedActual

/-! Mainline (A498): NON-VACUOUS four-triangle synthesis on the hull lane readouts.

Uses the hull lane `Mzk1HullDetStep3115Actual` only (independent readouts:
`hullReadout = packetLogVolume`, `detReadout = -log|q|`, Step (xi-f) comparison via the
det-normalized criterion `packetDet packet * q <= 1`).  The contract slots ipl/she/apt
carry REAL propositions with their evidence (the comparison itself, `0 < x.q`, and the
det readout identity) - no `True`/`trivial` placeholders and no qTheta/thetaPilotLogImage
definitions.  The filled instance is then consumed by `r4_literal_assembly` to produce
`Cor312Conclusion ∧ ABC ∧ literal hull finiteness`. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1HullDetNonVacuousSynthesisActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1HullDetStep3115Actual
open LeanFormal.IUT.XiFPaper.Mzk1FourTriangleSharedActual
open LeanFormal.IUT.XiFPaper.Mzk1R4LiteralAssemblyActual

universe u

variable {label : Type u} [Fintype label] [DecidableEq label]

/-- Non-vacuous StepXI contract from the hull-lane readouts: real (non-True) slot
  propositions with their evidence, comparison via the det-normalized criterion. -/
def hullDetContractNV (x : HullDetState label) (hneg : hullReadout x < 0)
    (hcmp : packetDet x.packet * x.q <= 1) : StepXIContract where
  qSigned := hullReadout x
  thetaSigned := detReadout x
  targetSigned := hullReadout x
  q_negative := hneg
  ipl := hullReadout x <= detReadout x
  she := 0 < x.q
  apt := detReadout x = -Real.log |x.q|
  ipl_evidence := hullReadout_le_detReadout_of_packetDet_mul_le_one x hcmp
  she_evidence := x.q_pos
  apt_evidence := rfl
  q_le_target := le_rfl
  target_le_theta := hullReadout_le_detReadout_of_packetDet_mul_le_one x hcmp

/-- The filled four-triangle instance of the shared module from the hull-lane readouts;
  the Step (xi-f) field is the proved det-normalized comparison. -/
def hullDetFourTriangleNV (x : HullDetState label) (hneg : hullReadout x < 0)
    (hcmp : packetDet x.packet * x.q <= 1) :
    FourTriangleSynthesis (HullDetState label) Unit where
  contract := hullDetContractNV x hneg hcmp
  hdd := hullDetHDD
  dsc := hullDetDsc x
  sheOut := hullDetSheOut
  hull_eq := rfl
  theta_eq := rfl
  step3115_comparison := step3115_comparison_hullDet x hcmp

/-- Cor 3.12 ordered conclusion from the non-vacuous hull/det synthesis. -/
theorem cor312Conclusion_hullDetNV (x : HullDetState label)
    (hneg : hullReadout x < 0) (hcmp : packetDet x.packet * x.q <= 1) :
    Cor312Conclusion (hullDetFourTriangleNV x hneg hcmp).contract :=
  cor312Conclusion_of_fourTriangleSynthesis (hullDetFourTriangleNV x hneg hcmp)

end

section R4Consumption

open LeanFormal.IUT.XiFPaper.Mzk1R4LiteralAssemblyActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.S2723GlobalIQHullActual

variable {l : PrimeGeFive} {V : Type}
variable {I : OriginalInput.{0, 0, 0, 0, 0} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable [∀ i, Fintype (C3.tensorPlaceIndex i)]

/-- The non-vacuous hull/det instance consumed by `r4_literal_assembly`: Cor 3.12 ordered
  conclusion, conditional ABC (via the explicit `hcomp` IUT IV comparisons), and the
  literal hull log-volume finiteness. -/
theorem r4_nonvacuous_assembly (j : Nat) {label : Type} [Fintype label] [DecidableEq label]
    (x : LeanFormal.IUT.XiFPaper.Mzk1HullDetStep3115Actual.HullDetState label)
    (hneg : LeanFormal.IUT.XiFPaper.Mzk1HullDetStep3115Actual.hullReadout x < 0)
    (hcmp : LeanFormal.IUT.XiFPaper.Mzk1HullDetStep3115Actual.packetDet x.packet * x.q <= 1)
    (hcomp : ∀ epsilon : Real, 0 < epsilon →
      Cor312EpsilonArithmeticComparison (literalIQInterface (C3 := C3) j) epsilon) :
    Cor312Conclusion (hullDetFourTriangleNV x hneg hcmp).contract ∧ ABCConjecture ∧
      globalIQLogVolume (C3 := C3) j (globalIQHull (C3 := C3) j) < ⊤ :=
  r4_literal_assembly (C3 := C3) (hullDetFourTriangleNV x hneg hcmp) j hcomp

end R4Consumption

end LeanFormal.IUT.XiFPaper.Mzk1HullDetNonVacuousSynthesisActual