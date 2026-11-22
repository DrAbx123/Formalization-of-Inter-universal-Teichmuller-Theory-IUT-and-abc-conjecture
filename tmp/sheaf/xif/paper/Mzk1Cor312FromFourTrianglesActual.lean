import tmp.sheaf.xif.paper.Mzk1FourTriangleObjectActual

/-! # Mzk1Cor312FromFourTrianglesActual — Cor 3.12 consumer of the four-triangle object

A518 interface/glue module (no new mathematics): connects the constructed four-triangle object
`Mzk1FourTriangleObjectActual.FourTriangleObject` to the Corollary 3.12 conclusion, exposing
the contract slots needed by the four-triangle synthesis route.  All content is projection /
consumer form of already-proved declarations.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312FromFourTrianglesActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.Mzk1FourTriangleSharedActual
open LeanFormal.IUT.XiFPaper.Mzk1HullDetStep3115Actual
open LeanFormal.IUT.XiFPaper.Mzk1HullDetFourTriangleActual
open LeanFormal.IUT.XiFPaper.Mzk1FourTriangleObjectActual

universe u
variable {label : Type u} [Fintype label] [DecidableEq label]
variable {l : PrimeGeFive}

/-- The contract of the constructed four-triangle object is the concrete hull/det contract. -/
theorem fourTriangleObject_contract_eq
    (T : SourceNativeInitialThetaData.{0} l) (x : HullDetState label)
    (hneg : hullReadout x < 0) (ipl : Prop) (hipl : ipl)
    (apt : Prop) (hapt : apt) (hcmp : packetDet x.packet * x.q <= 1) :
    (fourTriangleObject T x hneg ipl hipl apt hapt hcmp).synthesis.contract =
      hullDetContract T x hneg ipl hipl apt hapt hcmp := rfl

/-- **Cor 3.12 from the constructed four-triangle object**: the concrete contract satisfies
the IUT III Corollary 3.12 conclusion. -/
theorem cor312_of_fourTriangleObject
    (T : SourceNativeInitialThetaData.{0} l) (x : HullDetState label)
    (hneg : hullReadout x < 0) (ipl : Prop) (hipl : ipl)
    (apt : Prop) (hapt : apt) (hcmp : packetDet x.packet * x.q <= 1) :
    Cor312Conclusion (hullDetContract T x hneg ipl hipl apt hapt hcmp) :=
  hullDetFourTriangleConcrete_cor312 (T := T) x hneg ipl hipl apt hapt hcmp

/-- Consumer: the q/theta slots of the four-triangle contract are the hull/det readouts. -/
theorem fourTriangleContract_qSigned
    (T : SourceNativeInitialThetaData.{0} l) (x : HullDetState label)
    (hneg : hullReadout x < 0) (ipl : Prop) (hipl : ipl)
    (apt : Prop) (hapt : apt) (hcmp : packetDet x.packet * x.q <= 1) :
    (hullDetContract T x hneg ipl hipl apt hapt hcmp).qSigned = hullReadout x := rfl

/-- Consumer: the theta slot of the four-triangle contract is the det readout. -/
theorem fourTriangleContract_thetaSigned
    (T : SourceNativeInitialThetaData.{0} l) (x : HullDetState label)
    (hneg : hullReadout x < 0) (ipl : Prop) (hipl : ipl)
    (apt : Prop) (hapt : apt) (hcmp : packetDet x.packet * x.q <= 1) :
    (hullDetContract T x hneg ipl hipl apt hapt hcmp).thetaSigned = detReadout x := rfl

/-- Consumer: the four-triangle contract target is the hull log-volume. -/
theorem fourTriangleContract_targetSigned
    (T : SourceNativeInitialThetaData.{0} l) (x : HullDetState label)
    (hneg : hullReadout x < 0) (ipl : Prop) (hipl : ipl)
    (apt : Prop) (hapt : apt) (hcmp : packetDet x.packet * x.q <= 1) :
    (hullDetContract T x hneg ipl hipl apt hapt hcmp).targetSigned = hullReadout x := rfl

/-- Consumer: the q-pilot negativity slot of the four-triangle contract. -/
theorem fourTriangleContract_q_negative
    (T : SourceNativeInitialThetaData.{0} l) (x : HullDetState label)
    (hneg : hullReadout x < 0) (ipl : Prop) (hipl : ipl)
    (apt : Prop) (hapt : apt) (hcmp : packetDet x.packet * x.q <= 1) :
    (hullDetContract T x hneg ipl hipl apt hapt hcmp).qSigned < 0 := hneg

/-- Consumer: the q ≤ theta comparison of the four-triangle contract. -/
theorem fourTriangleContract_target_le_theta
    (T : SourceNativeInitialThetaData.{0} l) (x : HullDetState label)
    (hneg : hullReadout x < 0) (ipl : Prop) (hipl : ipl)
    (apt : Prop) (hapt : apt) (hcmp : packetDet x.packet * x.q <= 1) :
    (hullDetContract T x hneg ipl hipl apt hapt hcmp).targetSigned <=
      (hullDetContract T x hneg ipl hipl apt hapt hcmp).thetaSigned :=
  (hullDetContract T x hneg ipl hipl apt hapt hcmp).target_le_theta

#check fourTriangleObject_contract_eq
#check cor312_of_fourTriangleObject
#check fourTriangleContract_qSigned
#check fourTriangleContract_thetaSigned
#check fourTriangleContract_target_le_theta

end LeanFormal.IUT.XiFPaper.Mzk1Cor312FromFourTrianglesActual
end
