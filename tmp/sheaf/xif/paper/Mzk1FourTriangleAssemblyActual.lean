/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1FourTriangleObjectActual
import tmp.sheaf.xif.paper.Mzk1XiFFormalStepActual

/-!
# Mzk1FourTriangleAssemblyActual — four-triangle 3.12 assembly object

A518: assembly of the four triangles into one object over the green
`Mzk1FourTriangleObjectActual` and the abstract xi-f step:
* the fourth-triangle synthesis object (HDD ∘ SHE readout + Step (xi-f) comparison);
* the xi-e containment data for its contract;
* the assembled Cor 3.12 conclusion (`Cor312Conclusion`).

No new axiom, no comparison beyond the given containment. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.Mzk1FourTriangleAssemblyActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.Mzk1FourTriangleSharedActual
open LeanFormal.IUT.XiFPaper.Mzk1HullDetStep3115Actual
open LeanFormal.IUT.XiFPaper.Mzk1FourTriangleObjectActual
open LeanFormal.IUT.XiFPaper.Mzk1XiFFormalStepActual

universe u
variable {label : Type u} [Fintype label] [DecidableEq label]
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)

/-- The four-triangle assembly object: the fourth-triangle object plus the xi-e
containment for its contract. -/
structure FourTriangleAssembly where
  /-- the fourth-triangle object. -/
  object : FourTriangleObject label
  /-- xi-e containment for the assembled contract. -/
  containment : object.synthesis.contract.qSigned ∈
    regionLe object.synthesis.contract.thetaSigned

/-- The constructed assembly from a concrete state and the xi-e containment. -/
noncomputable def fourTriangleAssembly (x : HullDetState label)
    (hneg : hullReadout x < 0) (ipl : Prop) (hipl : ipl)
    (apt : Prop) (hapt : apt) (hcmp : packetDet x.packet * x.q <= 1)
    (hcont : (fourTriangleObject T x hneg ipl hipl apt hapt hcmp).synthesis.contract.qSigned ∈
      regionLe (fourTriangleObject T x hneg ipl hipl apt hapt hcmp).synthesis.contract.thetaSigned) :
    FourTriangleAssembly (label := label) :=
  { object := fourTriangleObject T x hneg ipl hipl apt hapt hcmp
    containment := hcont }

/-- The assembled Cor 3.12 conclusion from the xi-e containment. -/
theorem fourTriangleAssembly_cor312 (A : FourTriangleAssembly (label := label)) :
    Cor312Conclusion A.object.synthesis.contract :=
  xi_f_formal_step A.containment

/-- The assembly's fourth-triangle comparison (proved Step (xi-f)). -/
theorem fourTriangleAssembly_comparison (A : FourTriangleAssembly (label := label)) :
    (fourTriangleReadout A.object.synthesis.hdd A.object.synthesis.dsc
      A.object.synthesis.sheOut).1 ≤
      (fourTriangleReadout A.object.synthesis.hdd A.object.synthesis.dsc
        A.object.synthesis.sheOut).2 :=
  A.object.synthesis.step3115_comparison

/-- The assembly's contract q/theta slots are the readout pair. -/
theorem fourTriangleAssembly_hull_eq (A : FourTriangleAssembly (label := label)) :
    A.object.synthesis.contract.qSigned =
      (fourTriangleReadout A.object.synthesis.hdd A.object.synthesis.dsc
        A.object.synthesis.sheOut).1 :=
  A.object.synthesis.hull_eq

#check fourTriangleAssembly_cor312
#check fourTriangleAssembly_comparison

end LeanFormal.IUT.XiFPaper.Mzk1FourTriangleAssemblyActual
end
