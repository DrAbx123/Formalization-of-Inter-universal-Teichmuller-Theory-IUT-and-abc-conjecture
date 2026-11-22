import tmp.sheaf.xif.paper.Mzk1XiEContainmentRequirementActual

/-! # Annulus measure resolution of the last named xi-e input -/

namespace LeanFormal.IUT.XiFPaper.Mzk1AnnulusMeasureActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual

variable {α : Type*} {vol : Set α → Real}

/-- Annulus data: q region inside hull, with positive volume of the annulus
`hull \ q`. Additivity of the volume functional is a separate hypothesis. -/
structure XiEAnnulusData where
  qRegion : Set α
  hullRegion : Set α
  subset : qRegion ⊆ hullRegion
  q_pos : 0 < vol qRegion
  annulus_pos : 0 < vol (hullRegion \ qRegion)

/-- The annulus `hull \ q`. -/
def annulus (D : XiEAnnulusData (vol := vol)) : Set α :=
  D.hullRegion \ D.qRegion

/-- q region and annulus are disjoint. -/
theorem annulus_disjoint (D : XiEAnnulusData (vol := vol)) :
    Disjoint D.qRegion (annulus D) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  exact ((Set.mem_sdiff x).mp hx').2 hx

/-- q region union annulus is the hull. -/
theorem qRegion_union_annulus (D : XiEAnnulusData (vol := vol)) :
    D.qRegion ∪ annulus D = D.hullRegion := by
  ext x
  constructor
  · intro hx
    rcases hx with hx | hx
    · exact D.subset hx
    · exact ((Set.mem_sdiff x).mp hx).1
  · intro hx
    by_cases hq : x ∈ D.qRegion
    · exact Set.mem_union_left _ hq
    · exact Set.mem_union_right _ ((Set.mem_sdiff x).mpr ⟨hx, hq⟩)

/-- Positive annulus measure plus additivity resolves the strict_measure field. -/
theorem strictMeasure_of_annulus (D : XiEAnnulusData (vol := vol))
    (hadd : forall s t : Set α, Disjoint s t -> vol (s ∪ t) = vol s + vol t) :
    vol D.qRegion < vol D.hullRegion := by
  have hunion := qRegion_union_annulus D
  have h := hadd D.qRegion (annulus D) (annulus_disjoint D)
  have hann : 0 < vol (annulus D) := D.annulus_pos
  rw [← hunion, h]
  linarith [D.q_pos, hann]

/-- The annulus data instantiates the xi-e requirement with the derived strict
measure (last named input resolved into positive annulus measure). -/
noncomputable def requirementOfAnnulus (D : XiEAnnulusData (vol := vol))
    (hadd : forall s t : Set α, Disjoint s t -> vol (s ∪ t) = vol s + vol t) :
    XiEContainmentRequirement α vol where
  qRegion := D.qRegion
  thetaPossibleImages := D.qRegion
  hullRegion := D.hullRegion
  q_in_possible := fun _ hx => hx
  possible_in_hull := D.subset
  q_pos := D.q_pos
  strict_measure := strictMeasure_of_annulus D hadd

/-- The annulus instantiation has strict signed inequality. -/
theorem requirementOfAnnulus_strict (D : XiEAnnulusData (vol := vol))
    (hadd : forall s t : Set α, Disjoint s t -> vol (s ∪ t) = vol s + vol t) :
    requirementSignedQ (requirementOfAnnulus D hadd) <
      requirementSignedTheta (requirementOfAnnulus D hadd) :=
  requirement_strict_signed (requirementOfAnnulus D hadd)

end LeanFormal.IUT.XiFPaper.Mzk1AnnulusMeasureActual
