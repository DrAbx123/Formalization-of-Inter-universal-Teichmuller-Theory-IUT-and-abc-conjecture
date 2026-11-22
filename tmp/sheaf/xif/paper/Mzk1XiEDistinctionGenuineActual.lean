import tmp.sheaf.xif.paper.Mzk1KummerTransportActual
import tmp.sheaf.xif.paper.Mzk1XiEContainmentRequirementActual

/-! # Mzk1XiEDistinctionGenuineActual — honest xi-e requirement: genuine q_in_possible vs trivial possible_in_hull

A537 audit module: the honest form of the xi-e requirement takes the possible Theta
images to be the actual Theta hull itself.  Then `possible_in_hull` is reflexive, while
the genuine content is `q_in_possible` (the q-pilot singleton is contained in the hull,
proved by `qPilotInThetaCarrier_mem_hull`).  Both forms give the same signed values.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1XiEDistinctionGenuineActual

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

/-- The honest xi-e requirement: qRegion = {q-pilot image}, possible Theta images = hull,
hull region = hull.  Here `possible_in_hull` is reflexive and `q_in_possible` carries the
genuine containment. -/
noncomputable def genuineRequirement (D : KummerXiERealization T) :
    XiEContainmentRequirement (S1902Carrier T) D.vol where
  qRegion := {qPilotInThetaCarrier T}
  thetaPossibleImages := s1902Hull T
  hullRegion := s1902Hull T
  q_in_possible := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact qPilotInThetaCarrier_mem_hull T
  possible_in_hull := subset_rfl
  q_pos := D.q_pos
  strict_measure := D.strict_measure

/-- In the honest requirement `possible_in_hull` is reflexive (possible images = hull). -/
theorem genuine_possibleImages_eq_hull (D : KummerXiERealization T) :
    (genuineRequirement T D).thetaPossibleImages = (genuineRequirement T D).hullRegion :=
  rfl

/-- The genuine content of the honest requirement: the q-pilot singleton is contained
in the actual Theta hull (`q_in_possible` is NOT reflexive here). -/
theorem genuine_q_in_possible_genuine (D : KummerXiERealization T) :
    Set.Subset (genuineRequirement T D).qRegion (genuineRequirement T D).thetaPossibleImages :=
  qPilotInThetaCarrier_mem_hull T

/-- The signed q value is the same in the mainline form of the requirement. -/
theorem signedQ_eq_mainline (D : KummerXiERealization T) :
    requirementSignedQ (genuineRequirement T D) =
      Real.log (D.vol {qPilotInThetaCarrier T}) := by
  unfold requirementSignedQ signedLogVolume genuineRequirement
  rfl

/-- The signed Theta value is the same in the mainline form of the requirement. -/
theorem signedTheta_eq_mainline (D : KummerXiERealization T) :
    requirementSignedTheta (genuineRequirement T D) =
      Real.log (D.vol (s1902Hull T)) := by
  unfold requirementSignedTheta signedLogVolume genuineRequirement
  rfl

#check genuineRequirement
#check genuine_possibleImages_eq_hull
#check genuine_q_in_possible_genuine
#check signedQ_eq_mainline
#check signedTheta_eq_mainline

end LeanFormal.IUT.XiFPaper.Mzk1XiEDistinctionGenuineActual
end
