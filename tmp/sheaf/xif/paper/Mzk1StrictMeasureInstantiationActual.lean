import tmp.sheaf.xif.paper.Mzk1KummerTransportActual
import tmp.sheaf.xif.paper.Mzk1XiEContainmentRequirementActual

/-! # strict_measure instantiation from the Kummer xi-e realization -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StrictMeasureInstantiationActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1KummerTransportActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- `XiEContainmentRequirement` instantiated from a genuine Kummer xi-e
realization: `strict_measure` is the concrete `D.strict_measure` field. -/
noncomputable def requirementOfKummerRealization (D : KummerXiERealization T) :
    XiEContainmentRequirement (S1902Carrier T) D.vol where
  qRegion := {qPilotInThetaCarrier T}
  thetaPossibleImages := {qPilotInThetaCarrier T}
  hullRegion := s1902Hull T
  q_in_possible := fun _ hx => hx
  possible_in_hull := kummerXiE_containment (T := T) D
  q_pos := D.q_pos
  strict_measure := D.strict_measure

/-- The instantiated requirement has the strict signed inequality. -/
theorem strictMeasure_requirement_strict (D : KummerXiERealization T) :
    requirementSignedQ (requirementOfKummerRealization T D) <
      requirementSignedTheta (requirementOfKummerRealization T D) :=
  requirement_strict_signed (requirementOfKummerRealization T D)

/-- Consumer: the instantiated requirement yields `Cor312Conclusion`. -/
theorem strictMeasure_requirement_cor312 (D : KummerXiERealization T)
    (hqneg : requirementSignedQ (requirementOfKummerRealization T D) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (requirementContract (requirementOfKummerRealization T D) hqneg
        ipl hipl she hshe apt hapt) :=
  requirement_cor312 (requirementOfKummerRealization T D) hqneg ipl hipl she hshe apt hapt

end LeanFormal.IUT.XiFPaper.Mzk1StrictMeasureInstantiationActual
