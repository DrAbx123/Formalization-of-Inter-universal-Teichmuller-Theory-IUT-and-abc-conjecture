import tmp.sheaf.xif.paper.Mzk1Cor312ResolvedStrictAcceptanceV3Actual
import tmp.sheaf.xif.paper.Mzk1Cor312AcceptanceV4Actual

/-! # Resolved acceptance V2: clean wrap-up record over green V3/V4 -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312AcceptanceResolvedV2

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1PositiveMeasureQRegionProofActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312ResolvedStrictAcceptanceV3Actual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312AcceptanceV4Actual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- V2 resolved strict: strict_measure derived from positive Haar (V3). -/
theorem resolvedV2_strict (D : PositiveQRegionHaarStrict T) :
    qNormalizedVolume T (qRegion T) < qNormalizedVolume T (s1902Hull T) :=
  resolved_strict_measure T D

/-- V2 resolved Cor 3.12 conclusion (V3). -/
theorem resolvedV2_cor312 (D : PositiveQRegionHaarStrict T)
    (hqneg : requirementSignedQ (resolvedRequirement T D) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (requirementContract (resolvedRequirement T D) hqneg ipl hipl she hshe apt hapt) :=
  resolved_cor312 T D hqneg ipl hipl she hshe apt hapt

/-- V2 paper Cor 3.12 conclusion (V4). -/
theorem paperV2_cor312 (R : PaperKummerReading T)
    (hqneg : requirementSignedQ (requirementOfReading T R) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion (cor312Contract_final T R hqneg ipl hipl she hshe apt hapt) :=
  Mzk1Cor312AcceptanceV4Actual.cor312_conclusion T R hqneg ipl hipl she hshe apt hapt

/- V2 axiom gate: both acceptance paths depend only on the allowed axioms. -/
#print axioms resolved_cor312
#print axioms Mzk1Cor312AcceptanceV4Actual.cor312_conclusion

end LeanFormal.IUT.XiFPaper.Mzk1Cor312AcceptanceResolvedV2
