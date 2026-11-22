import tmp.sheaf.xif.paper.Mzk1KummerTransportActual
import tmp.sheaf.xif.paper.Mzk1XiEContainmentRequirementActual

/-! # Mzk1XiEDistinctionMainlineActual — mainline xi-e requirement: trivial q_in_possible vs genuine possible_in_hull

A537 audit module: in the mainline xi-e requirement the `q_in_possible` field is
DISCHARGED BY REFLEXIVITY (qRegion and thetaPossibleImages are both the singleton of
the realized q-pilot image), while the genuine xi-e content is the `possible_in_hull`
field (the singleton is contained in the actual Theta hull, proved by
`kummerXiE_containment`).  This file makes that distinction explicit.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1XiEDistinctionMainlineActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1KummerTransportActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1SignedLogVolumeCor312Actual
open LeanFormal.IUT.XiFPaper.Mzk1SignedCor312ContractActual
open scoped BigOperators

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The mainline-style xi-e requirement: qRegion = thetaPossibleImages = {q-pilot image}.
The `q_in_possible` field is purely reflexive here; the genuine content is
`possible_in_hull`. -/
noncomputable def mainlineRequirement (D : KummerXiERealization T) :
    XiEContainmentRequirement (S1902Carrier T) D.vol where
  qRegion := {qPilotInThetaCarrier T}
  thetaPossibleImages := {qPilotInThetaCarrier T}
  hullRegion := s1902Hull T
  q_in_possible := fun _ hx => hx
  possible_in_hull := kummerXiE_containment (T := T) D
  q_pos := D.q_pos
  strict_measure := D.strict_measure

/-- In the mainline requirement the q-region and the possible Theta images coincide,
so that `q_in_possible` is indeed discharged by reflexivity. -/
theorem mainline_qRegion_eq_possibleImages (D : KummerXiERealization T) :
    (mainlineRequirement T D).qRegion = (mainlineRequirement T D).thetaPossibleImages :=
  rfl

/-- The genuine xi-e content of the mainline requirement: the q-pilot singleton is
contained in the actual Theta hull (`possible_in_hull` is NOT reflexive here). -/
theorem mainline_possible_in_hull_genuine (D : KummerXiERealization T) :
    Set.Subset (mainlineRequirement T D).thetaPossibleImages
      (mainlineRequirement T D).hullRegion :=
  kummerXiE_containment (T := T) D

/-- The mainline requirement does not put the singleton in the hull definitionally:
the containment is the proved genuine xi-e statement, exposed separately. -/
theorem mainline_xi_e_content (D : KummerXiERealization T) :
    {qPilotInThetaCarrier T} ⊆ s1902Hull T :=
  kummerXiE_containment (T := T) D

#check mainlineRequirement
#check mainline_qRegion_eq_possibleImages
#check mainline_possible_in_hull_genuine
#check mainline_xi_e_content

end LeanFormal.IUT.XiFPaper.Mzk1XiEDistinctionMainlineActual
end
