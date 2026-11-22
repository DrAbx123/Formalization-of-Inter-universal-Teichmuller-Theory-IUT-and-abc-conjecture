import tmp.sheaf.xif.paper.Mzk1Cor312ResolvedStrictAcceptanceV3Actual
import tmp.sheaf.xif.paper.Mzk1Cor312AcceptanceInterfaceActual

/-! # Resolved requirement acceptance (V3 resolvedRequirement) -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312ResolvedRequirementAcceptanceActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1PositiveMeasureQRegionProofActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312ResolvedStrictAcceptanceV3Actual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312AcceptanceInterfaceActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Resolved requirement: q_pos is a theorem (positive Haar volume of qRegion). -/
theorem resolved_requirement_q_pos (D : PositiveQRegionHaarStrict T) :
    0 < qNormalizedVolume T (qRegion T) :=
  resolved_q_pos T D

/-- Resolved requirement: strict_measure is derived from positive Haar. -/
theorem resolved_requirement_strict (D : PositiveQRegionHaarStrict T) :
    qNormalizedVolume T (qRegion T) < qNormalizedVolume T (s1902Hull T) :=
  resolved_strict_measure T D

/-- Resolved requirement: signed inequality (paper shape). -/
theorem resolved_requirement_paper (D : PositiveQRegionHaarStrict T) :
    requirementSignedQ (resolvedRequirement T D) ≤
      requirementSignedTheta (resolvedRequirement T D) :=
  resolved_paper_inequality T D

/-- Resolved requirement: strict signed inequality (non-vacuity). -/
theorem resolved_requirement_strict_signed (D : PositiveQRegionHaarStrict T) :
    requirementSignedQ (resolvedRequirement T D) <
      requirementSignedTheta (resolvedRequirement T D) :=
  resolved_paper_inequality_strict T D

/-- Resolved requirement: `Cor312Conclusion` consumer. -/
theorem resolved_requirement_cor312 (D : PositiveQRegionHaarStrict T)
    (hqneg : requirementSignedQ (resolvedRequirement T D) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (requirementContract (resolvedRequirement T D) hqneg ipl hipl she hshe apt hapt) :=
  resolved_cor312 T D hqneg ipl hipl she hshe apt hapt

/-- Resolved requirement: `C_Theta >= -1` consumer. -/
theorem resolved_requirement_CTheta (D : PositiveQRegionHaarStrict T)
    (hqneg : requirementSignedQ (resolvedRequirement T D) < 0) {C : Real}
    (hC : requirementSignedTheta (resolvedRequirement T D) ≤
      C * (-requirementSignedQ (resolvedRequirement T D))) : -1 ≤ C :=
  acceptance_CTheta (resolvedRequirement T D) hqneg hC

/-- Axiom gate for the resolved requirement acceptance. -/
#print axioms resolved_requirement_q_pos
#print axioms resolved_requirement_strict
#print axioms resolved_requirement_cor312
#print axioms resolved_requirement_CTheta

end LeanFormal.IUT.XiFPaper.Mzk1Cor312ResolvedRequirementAcceptanceActual
