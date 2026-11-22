/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HullDetFourTriangleActual

/-!
# Mzk1FourTriangleObjectActual — four-triangle objects for 3.11.5 =⇒ 3.12

A517: reference object packing the four triangles of the formalization route:
* triangle 1/2: raw/multiradial input-output (handled in `Mzk1MRRepObjectActual`/LANA);
* triangle 3 `(HDD) := (hull+det)∘(dsc)`: `hullDetHDD`, `hullDetDsc`;
* triangle 4 `(HDD)∘(SHE)`: `fourTriangleReadout hullDetHDD hullDetDsc hullDetSheOut`
  with the proved Step (xi-f) comparison from `packetDet packet * q ≤ 1`;
* the shared-B `FourTriangleSynthesis` and its Cor 3.12 conclusion.

All objects are the actual green definitions of `Mzk1HullDetStep3115Actual` /
`Mzk1FourTriangleSharedActual`; no new axiom, no vacuous target. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.Mzk1FourTriangleObjectActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.Mzk1FourTriangleSharedActual
open LeanFormal.IUT.XiFPaper.Mzk1HullDetStep3115Actual
open LeanFormal.IUT.XiFPaper.Mzk1HullDetFourTriangleActual

universe u
variable {label : Type u} [Fintype label] [DecidableEq label]
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)

/-- The four-triangle object: state + contract/synthesis data of the fourth triangle. -/
structure FourTriangleObject (label : Type u) [Fintype label] where
  /-- the concrete hull/det state. -/
  state : HullDetState label
  /-- Step (xi-f) comparison input. -/
  hcmp : packetDet state.packet * state.q <= 1
  /-- the induced shared-B synthesis (fourth triangle). -/
  synthesis : FourTriangleSynthesis (HullDetState label) Unit

/-- The fourth triangle's readout pair `(hull, det)`. -/
def fourTriangleObject_readout (x : HullDetState label) : Real × Real :=
  fourTriangleReadout hullDetHDD (hullDetDsc x) hullDetSheOut

/-- The readout is the hull/det pair (definitional). -/
theorem fourTriangleObject_readout_eq (x : HullDetState label) :
    fourTriangleObject_readout (label := label) x =
      (hullReadout x, detReadout x) := rfl

/-- The proved Step (xi-f) comparison of the fourth triangle. -/
theorem fourTriangleObject_comparison (x : HullDetState label)
    (hcmp : packetDet x.packet * x.q <= 1) :
    (fourTriangleReadout hullDetHDD (hullDetDsc x) hullDetSheOut).1 ≤
      (fourTriangleReadout hullDetHDD (hullDetDsc x) hullDetSheOut).2 :=
  step3115_comparison_hullDet x hcmp

/-- The constructed four-triangle object from a concrete state and comparison input. -/
noncomputable def fourTriangleObject (T : SourceNativeInitialThetaData.{0} l) (x : HullDetState label)
    (hneg : hullReadout x < 0) (ipl : Prop) (hipl : ipl)
    (apt : Prop) (hapt : apt) (hcmp : packetDet x.packet * x.q <= 1) :
    FourTriangleObject label where
  state := x
  hcmp := hcmp
  synthesis := hullDetFourTriangleConcrete (T := T) x hneg ipl hipl apt hapt hcmp

/-- `_constructed`: the synthesis is the concrete shared-B wiring. -/
theorem fourTriangleObject_constructed (T : SourceNativeInitialThetaData.{0} l) (x : HullDetState label)
    (hneg : hullReadout x < 0) (ipl : Prop) (hipl : ipl)
    (apt : Prop) (hapt : apt) (hcmp : packetDet x.packet * x.q <= 1) :
    (fourTriangleObject T x hneg ipl hipl apt hapt hcmp).synthesis =
      hullDetFourTriangleConcrete (T := T) x hneg ipl hipl apt hapt hcmp := rfl

/-- The Cor 3.12 conclusion from the four-triangle object. -/
theorem fourTriangleObject_cor312 (O : FourTriangleObject label) :
    Cor312Conclusion O.synthesis.contract :=
  cor312Conclusion_of_fourTriangleSynthesis O.synthesis

/-- Triangle 4 readout equality: the contract's q/theta slots are the fourth
triangle's readout. -/
theorem fourTriangleObject_hull_eq (O : FourTriangleObject label) :
    O.synthesis.contract.qSigned =
      (fourTriangleReadout O.synthesis.hdd O.synthesis.dsc O.synthesis.sheOut).1 := 
  O.synthesis.hull_eq

#check fourTriangleObject_readout_eq
#check fourTriangleObject_comparison
#check fourTriangleObject_cor312

end LeanFormal.IUT.XiFPaper.Mzk1FourTriangleObjectActual
end
