import tmp.sheaf.xif.paper.Mzk1XiEContainmentRequirementActual

/-! # Mzk1StrictMeasureDerivedActual — deriving strict_measure from strict volume monotonicity

A551 module (no new mathematics): the `strict_measure` field of the non-vacuous xi-e
requirement can be DERIVED, rather than assumed, from (i) strict monotonicity of the
volume functional on proper subset pairs and (ii) proper containment `qRegion ⊊ hullRegion`.
This makes the non-vacuity content explicit: a positive-measure q-region properly inside
a strictly larger hull.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1StrictMeasureDerivedActual

open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual

universe u

/-- Strict volume monotonicity data: the volume strictly increases on proper inclusions. -/
structure StrictVolMono (α : Type u) (vol : Set α → Real) : Prop where
  mono : ∀ {S T : Set α}, S ⊆ T → vol S ≤ vol T
  strict_of_ssubset : ∀ {S T : Set α}, S ⊂ T → vol S < vol T

/-- Replacing the `strict_measure` field by strict monotonicity + proper containment:
given regions with `qRegion ⊆ thetaPossibleImages ⊆ hullRegion` where the q-region is a
PROPER subset of the hull, strict_measure is derived. -/
noncomputable def requirementOfStrictVol {α : Type u} {vol : Set α → Real}
    (D : StrictVolMono α vol) (qRegion thetaPossibleImages hullRegion : Set α)
    (hqpos : 0 < vol qRegion) (h1 : qRegion ⊆ thetaPossibleImages)
    (h2 : thetaPossibleImages ⊆ hullRegion) (hproper : qRegion ⊂ hullRegion) :
    XiEContainmentRequirement α vol where
  qRegion := qRegion
  thetaPossibleImages := thetaPossibleImages
  hullRegion := hullRegion
  q_in_possible := h1
  possible_in_hull := h2
  q_pos := hqpos
  strict_measure := D.strict_of_ssubset hproper

/-- The derived requirement satisfies the strict signed comparison. -/
theorem derived_strict_signed {α : Type u} {vol : Set α → Real}
    (D : StrictVolMono α vol) (qRegion thetaPossibleImages hullRegion : Set α)
    (hqpos : 0 < vol qRegion) (h1 : qRegion ⊆ thetaPossibleImages)
    (h2 : thetaPossibleImages ⊆ hullRegion) (hproper : qRegion ⊂ hullRegion) :
    requirementSignedQ (requirementOfStrictVol D qRegion thetaPossibleImages
      hullRegion hqpos h1 h2 hproper) <
    requirementSignedTheta (requirementOfStrictVol D qRegion thetaPossibleImages
      hullRegion hqpos h1 h2 hproper) :=
  requirement_strict_signed _

#check StrictVolMono
#check requirementOfStrictVol
#check derived_strict_signed

end LeanFormal.IUT.XiFPaper.Mzk1StrictMeasureDerivedActual
end
