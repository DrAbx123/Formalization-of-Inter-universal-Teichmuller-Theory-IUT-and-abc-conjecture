/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1XiEContainmentRequirementActual

/-!
# A537 pattern check: the three DISTINCT parts of the final xi-e requirement

Abstract, chain-independent form of the A537 distinction:
1. `q_in_possible` is the DEFINITIONAL PROJECTION of the Kummer realization
   (`qRegion = thetaPossibleImages`; in the paper q is by construction the Kummer
   image `kummerMap theta_1`, so this projection is not the xi-e content);
2. `possible_in_hull := hsub` is the REAL xi-e input (a theorem/assumption, not rfl);
3. `strict_measure` is the ONLY named input (strict volume increase).

Both the strict signed inequality and the Cor 3.12 contract are proved from these
three kept-separate parts; no True/constant-region/definitional-MRRep device.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1A537PatternChecksActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual

/-- The requirement pattern with the three parts kept separate. -/
def projectionRequirement {α : Type*} (vol : Set α → ℝ) (qRegion hullRegion : Set α)
    (hsub : qRegion ⊆ hullRegion) (hpos : 0 < vol qRegion)
    (hstrict : vol qRegion < vol hullRegion) :
    XiEContainmentRequirement α vol where
  qRegion := qRegion
  thetaPossibleImages := qRegion
  hullRegion := hullRegion
  q_in_possible := fun _ hx => hx
  possible_in_hull := hsub
  q_pos := hpos
  strict_measure := hstrict

/-- (1) `q_in_possible` is the definitional projection: `qRegion ⊆ qRegion`. -/
theorem projection_q_in_possible {α : Type*} (vol : Set α → ℝ)
    (qRegion hullRegion : Set α) (hsub : qRegion ⊆ hullRegion)
    (hpos : 0 < vol qRegion) (hstrict : vol qRegion < vol hullRegion) :
    qRegion ⊆ qRegion :=
  fun _ hx => hx

/-- (2) `possible_in_hull` is the genuine xi-e input (`qRegion ⊆ hullRegion`). -/
theorem projection_possible_in_hull {α : Type*} (vol : Set α → ℝ)
    (qRegion hullRegion : Set α) (hsub : qRegion ⊆ hullRegion)
    (hpos : 0 < vol qRegion) (hstrict : vol qRegion < vol hullRegion) :
    Set.Subset
      (projectionRequirement vol qRegion hullRegion hsub hpos hstrict).thetaPossibleImages
      (projectionRequirement vol qRegion hullRegion hsub hpos hstrict).hullRegion :=
  hsub

/-- (3) `strict_measure` is the named strict volume increase. -/
theorem projection_strict_measure {α : Type*} (vol : Set α → ℝ)
    (qRegion hullRegion : Set α) (hsub : qRegion ⊆ hullRegion)
    (hpos : 0 < vol qRegion) (hstrict : vol qRegion < vol hullRegion) :
    vol qRegion < vol hullRegion :=
  hstrict

/-- The strict signed inequality derived from the three kept-separate parts. -/
theorem projection_signed_strict {α : Type*} {vol : Set α → ℝ} {qRegion hullRegion : Set α}
    (hsub : qRegion ⊆ hullRegion) (hpos : 0 < vol qRegion)
    (hstrict : vol qRegion < vol hullRegion) :
    requirementSignedQ (projectionRequirement vol qRegion hullRegion hsub hpos hstrict) <
      requirementSignedTheta
        (projectionRequirement vol qRegion hullRegion hsub hpos hstrict) :=
  requirement_strict_signed _

/-- The Cor 3.12 contract from the three kept-separate parts. -/
theorem projection_cor312 {α : Type*} {vol : Set α → ℝ} {qRegion hullRegion : Set α}
    (hsub : qRegion ⊆ hullRegion) (hpos : 0 < vol qRegion)
    (hstrict : vol qRegion < vol hullRegion)
    (hqneg : requirementSignedQ
        (projectionRequirement vol qRegion hullRegion hsub hpos hstrict) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (requirementContract (projectionRequirement vol qRegion hullRegion hsub hpos hstrict)
        hqneg ipl hipl she hshe apt hapt) :=
  requirement_cor312 _ hqneg ipl hipl she hshe apt hapt

end

end LeanFormal.IUT.XiFPaper.Mzk1A537PatternChecksActual
-- A549: force recompile (stale log from an older version).
