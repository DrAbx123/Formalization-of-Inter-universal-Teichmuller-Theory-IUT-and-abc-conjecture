/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HullDetFourTriangleActual

/-!
# Mzk1HullDetObjectActual — actual hull+det object (3.12 right-hand side)

A517 object file reusing our green assets (`Mzk1HullDetStep3115Actual` +
`Mzk1HullDetFourTriangleActual`):
* the concrete hull/det state object with `hullReadout`/`detReadout`;
* the HDD decomposition object `hullDetHDD`;
* the proved det-normalized comparison `hullReadout ≤ detReadout` from
  `packetDet packet * q ≤ 1` (`step3115_comparison_hullDet`);
* the shared-B `FourTriangleSynthesis` wiring (`hullDetFourTriangleConcrete`).

No new axiom, no comparison beyond the proved Step (xi-f) one. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.Mzk1HullDetObjectActual

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

/-- The concrete hull/det object: a state with hull negativity and the
det-normalized comparison input `packetDet packet * q ≤ 1`. -/
structure HullDetObject (label : Type u) [Fintype label] [DecidableEq label] where
  state : HullDetState label
  hneg : hullReadout state < 0
  hcmp : packetDet state.packet * state.q <= 1

/-- The constructed hull/det object. -/
def hullDetObject (x : HullDetState label) (hneg : hullReadout x < 0)
    (hcmp : packetDet x.packet * x.q <= 1) : HullDetObject label where
  state := x
  hneg := hneg
  hcmp := hcmp

/-- `_constructed`: the object's state is the given concrete state. -/
theorem hullDetObject_constructed (x : HullDetState label)
    (hneg : hullReadout x < 0) (hcmp : packetDet x.packet * x.q <= 1) :
    (hullDetObject x hneg hcmp).state = x := rfl

/-- The HDD decomposition of the hull/det object. -/
def hullDetObject_hdd (O : HullDetObject label) :
    HDDDecomp Real Real (HullDetState label) := hullDetHDD

/-- The readout pair of the decomposition. -/
theorem hullDetObject_readout (O : HullDetObject label) :
    HDD hullDetHDD O.state =
      (hullReadout O.state, detReadout O.state) := rfl

/-- The proved det-normalized comparison: the hull readout is ≤ the det readout. -/
theorem hullDetObject_comparison (O : HullDetObject label) :
    (fourTriangleReadout hullDetHDD (hullDetDsc O.state) hullDetSheOut).1 ≤
      (fourTriangleReadout hullDetHDD (hullDetDsc O.state) hullDetSheOut).2 :=
  step3115_comparison_hullDet O.state O.hcmp

/-- The shared four-triangle synthesis from the hull/det object (concrete wiring). -/
noncomputable def hullDetObject_synthesis (T : SourceNativeInitialThetaData.{0} l) (O : HullDetObject label)
    (ipl : Prop) (hipl : ipl) (apt : Prop) (hapt : apt) :
    FourTriangleSynthesis (HullDetState label) Unit :=
  hullDetFourTriangleConcrete (T := T) O.state O.hneg ipl hipl apt hapt O.hcmp

/-- Cor 3.12 conclusion from the hull/det object's shared synthesis. -/
theorem hullDetObject_cor312 (T : SourceNativeInitialThetaData.{0} l) (O : HullDetObject label)
    (ipl : Prop) (hipl : ipl) (apt : Prop) (hapt : apt) :
    Cor312Conclusion (hullDetObject_synthesis T O ipl hipl apt hapt).contract :=
  cor312Conclusion_of_fourTriangleSynthesis _

#check hullDetObject_comparison
#check hullDetObject_synthesis
#check hullDetObject_cor312

end LeanFormal.IUT.XiFPaper.Mzk1HullDetObjectActual
end
