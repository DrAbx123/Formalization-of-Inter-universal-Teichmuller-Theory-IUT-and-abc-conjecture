import tmp.sheaf.xif.paper.Mzk1XiEContainmentRequirementActual

/-! # Positive-measure qRegion resolves `strict_measure` -/

namespace LeanFormal.IUT.XiFPaper.Mzk1StrictMeasurePositiveMeasureActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual

variable {α : Type*} {vol : Set α → Real}

/-- Data with a positive-volume extra region disjoint from the q region, giving the
strict volume increase of the xi-e hull. -/
structure XiEVolumeData where
  qRegion : Set α
  hullRegion : Set α
  delta : Set α
  subset : qRegion ≤ hullRegion
  hull_eq : hullRegion = qRegion ∪ delta
  disjoint : Disjoint qRegion delta
  q_pos : 0 < vol qRegion
  delta_pos : 0 < vol delta
  vol_union : forall s t : Set α, Disjoint s t -> vol (s ∪ t) = vol s + vol t

/-- Positive extra measure plus additivity resolves the named `strict_measure`. -/
theorem strictMeasure_of_positive_extra (D : XiEVolumeData (vol := vol)) :
    vol D.qRegion < vol D.hullRegion := by
  rw [D.hull_eq, D.vol_union D.qRegion D.delta D.disjoint]
  linarith [D.q_pos, D.delta_pos]

/-- The volume data instantiates `XiEContainmentRequirement` with the derived
`strict_measure` (not a named input). -/
noncomputable def requirementOfVolumeData (D : XiEVolumeData (vol := vol)) :
    XiEContainmentRequirement α vol where
  qRegion := D.qRegion
  thetaPossibleImages := D.qRegion
  hullRegion := D.hullRegion
  q_in_possible := fun _ hx => hx
  possible_in_hull := D.subset
  q_pos := D.q_pos
  strict_measure := strictMeasure_of_positive_extra D

/-- The instantiated requirement has the genuine strict signed inequality. -/
theorem requirementOfVolumeData_strict (D : XiEVolumeData (vol := vol)) :
    requirementSignedQ (requirementOfVolumeData D) <
      requirementSignedTheta (requirementOfVolumeData D) :=
  requirement_strict_signed (requirementOfVolumeData D)

end LeanFormal.IUT.XiFPaper.Mzk1StrictMeasurePositiveMeasureActual
