import tmp.sheaf.xif.paper.Mzk1Cor312ResolvedStrictAcceptanceV3Actual
import tmp.sheaf.xif.paper.Mzk1Cor312AcceptanceV4Actual
import tmp.sheaf.xif.paper.Mzk1XiEContainmentRequirementActual
import tmp.sheaf.xif.paper.Mzk1Cor312AcceptanceInterfaceActual
import tmp.sheaf.xif.paper.Mzk1AnnulusMeasureActual

/-! # Cor 3.12 acceptance_final: resolved (V3) and paper (V4) consumers -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312AcceptanceFinalActual

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
open LeanFormal.IUT.XiFPaper.Mzk1Cor312AcceptanceInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1AnnulusMeasureActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Resolved acceptance_final (V3): strict_measure derived from positive Haar, only
`haarStrict`/readout remain named. -/
theorem acceptanceFinal_resolved (D : PositiveQRegionHaarStrict T)
    (hqneg : requirementSignedQ (resolvedRequirement T D) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (requirementContract (resolvedRequirement T D) hqneg ipl hipl she hshe apt hapt) :=
  resolved_cor312 T D hqneg ipl hipl she hshe apt hapt

/-- Paper acceptance_final (V4): final assembly conclusion through the paper reading. -/
theorem acceptanceFinal_paper (R : PaperKummerReading T)
    (hqneg : requirementSignedQ (requirementOfReading T R) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion (cor312Contract_final T R hqneg ipl hipl she hshe apt hapt) :=
  Mzk1Cor312AcceptanceV4Actual.cor312_conclusion T R hqneg ipl hipl she hshe apt hapt

/-- Standard path: generic `XiEContainmentRequirement` gives `Cor312Conclusion`. -/
theorem standard_path_cor312 {α : Type*} {vol : Set α → Real}
    (D : XiEContainmentRequirement α vol)
    (hqneg : requirementSignedQ D < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion (requirementContract D hqneg ipl hipl she hshe apt hapt) :=
  acceptance_cor312 D hqneg ipl hipl she hshe apt hapt

/-- Standard path: signed paper inequality. -/
theorem standard_path_paper {α : Type*} {vol : Set α → Real}
    (D : XiEContainmentRequirement α vol) :
    requirementSignedQ D ≤ requirementSignedTheta D :=
  acceptance_paper_inequality D

/-- Standard path: strict signed inequality (non-vacuity). -/
theorem standard_path_strict {α : Type*} {vol : Set α → Real}
    (D : XiEContainmentRequirement α vol) :
    requirementSignedQ D < requirementSignedTheta D :=
  acceptance_paper_inequality_strict D

/-- Standard path: `C_Theta >= -1` form. -/
theorem standard_path_CTheta {α : Type*} {vol : Set α → Real}
    (D : XiEContainmentRequirement α vol)
    (hqneg : requirementSignedQ D < 0) {C : Real}
    (hC : requirementSignedTheta D ≤ C * (-requirementSignedQ D)) : -1 ≤ C :=
  acceptance_CTheta D hqneg hC

/-- Readings path: paper reading inequality from the genuine Kummer realization. -/
theorem readings_path_paper (R : PaperKummerReading T) :
    R.qReading ≤ R.thetaReading :=
  le_of_lt (paperKummerReading_strict T R)

/-- Readings path: `C_Theta >= -1` from the strict paper reading. -/
theorem readings_path_CTheta (R : PaperKummerReading T) (hqneg : R.qReading < 0)
    {C : Real} (hC : R.thetaReading ≤ C * (-R.qReading)) : -1 ≤ C :=
  Mzk1Cor312AcceptanceV4Actual.acceptance_CTheta T R hqneg hC


section ResolvedPath

variable {α : Type*} {vol : Set α → Real}

/-- Resolved path: strict signed inequality from the annulus-instantiated requirement. -/

theorem resolved_path_strict (D : XiEAnnulusData (vol := vol))
    (hadd : forall s t : Set α, Disjoint s t -> vol (s ∪ t) = vol s + vol t) :
    requirementSignedQ (requirementOfAnnulus (vol := vol) D hadd) <
      requirementSignedTheta (requirementOfAnnulus (vol := vol) D hadd) :=
  requirementOfAnnulus_strict D hadd

/-- Resolved path: `Cor312Conclusion` from the annulus-instantiated requirement. -/
theorem resolved_path_cor312 (D : XiEAnnulusData (vol := vol))
    (hadd : forall s t : Set α, Disjoint s t -> vol (s ∪ t) = vol s + vol t)
    (hqneg : requirementSignedQ (requirementOfAnnulus (vol := vol) D hadd) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (requirementContract (requirementOfAnnulus (vol := vol) D hadd) hqneg
        ipl hipl she hshe apt hapt) :=
  acceptance_cor312 (requirementOfAnnulus (vol := vol) D hadd) hqneg
    ipl hipl she hshe apt hapt

/-- **acceptance_final**: four-in-one: standard path conclusion, signed paper inequality,
resolved strict inequality, and the C_Theta >= -1 form. -/
theorem acceptance_final (D : XiEContainmentRequirement α vol)
    (R : XiEAnnulusData (vol := vol))
    (hadd : forall s t : Set α, Disjoint s t -> vol (s ∪ t) = vol s + vol t)
    (hqneg : requirementSignedQ D < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion (requirementContract D hqneg ipl hipl she hshe apt hapt) ∧
      (requirementSignedQ D ≤ requirementSignedTheta D) ∧
      (requirementSignedQ (requirementOfAnnulus (vol := vol) R hadd) <
        requirementSignedTheta (requirementOfAnnulus (vol := vol) R hadd)) ∧
      (forall C : Real,
        requirementSignedTheta D ≤ C * (-requirementSignedQ D) -> -1 ≤ C) :=
  ⟨standard_path_cor312 D hqneg ipl hipl she hshe apt hapt,
   standard_path_paper D,
   resolved_path_strict R hadd,
   fun C hC => standard_path_CTheta D hqneg hC⟩

end ResolvedPath

/- Axiom gate: acceptance_final path declarations. -/
#print axioms standard_path_cor312
#print axioms resolved_path_cor312
#print axioms acceptance_final

end LeanFormal.IUT.XiFPaper.Mzk1Cor312AcceptanceFinalActual
