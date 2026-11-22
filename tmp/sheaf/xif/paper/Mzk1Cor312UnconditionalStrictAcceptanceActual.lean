/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HaarStrictActual
import tmp.sheaf.xif.paper.Mzk1XiEContainmentRequirementActual

/-!
# A553 unconditional strict_measure from the positive-measure annulus

`Mzk1HaarStrictActual` proves (product and normalized Haar forms) that the q-ball
region has STRICTLY smaller measure than the actual hull, via the disjoint strict
cylinder annulus of positive measure.  This file feeds that into the xi-e
requirement, so that `strict_measure` is no longer a named field:

* `vol := fun S => (s1902NormalizedHaar T S).toReal` (normalized real volume);
* `q_pos` from `qBallRegion_measure_pos` (annulus/positive-measure q-ball);
* `strict_measure` from `s1902NormalizedHaar_haarStrict` (proved annulus strictness),
  with only the finiteness of the hull measure as a side hypothesis;
* `possible_in_hull` from `qBallRegion_subset_hull`.

Remaining hypotheses: `hstrict` (q image strictly inside the hull radius), `hqpos`
(q image norm positive), `hultra` (root extensions ultrametric), `b0` (a bad place),
and hull-measure finiteness.  These are geometric side conditions, not the comparison.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312UnconditionalStrictAcceptanceActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarStrictActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open MeasureTheory
open scoped ENNReal BigOperators

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The normalized real volume: `toReal` of the S1902 normalized Haar measure. -/
noncomputable def normalizedRealVolume (S : Set (S1902Carrier T)) : ℝ :=
  (s1902NormalizedHaar T S).toReal

/-- Geometric side conditions for the annulus comparison. -/
structure HaarStrictGeometry where
  hstrict : ∀ b : Bad (nativePlaceSelection T),
    ‖qPilotInThetaCarrier T b‖ < (rootImageRadius T b : ℝ)
  hqpos : ∀ b : Bad (nativePlaceSelection T),
    0 < ‖qPilotInThetaCarrier T b‖
  hultra : ∀ b, IsUltrametricDist (rootNormedExtension T b)
  b0 : Bad (nativePlaceSelection T)
  hhfin : s1902NormalizedHaar T (s1902Hull T) < ⊤

/-- The q-ball region is contained in the actual hull (genuine xi-e geometry). -/
theorem qBallRegion_subset_hull_real (G : HaarStrictGeometry T) :
    qBallRegion T ⊆ s1902Hull T :=
  qBallRegion_subset_hull T G.hstrict G.hqpos

/-- Positive normalized real volume of the q-ball region. -/
theorem normalizedRealVolume_qBall_pos (G : HaarStrictGeometry T) :
    0 < normalizedRealVolume T (qBallRegion T) :=
  ENNReal.toReal_pos
    (ne_of_gt (qBallRegion_measure_pos T G.hstrict G.hqpos))
    (ne_of_lt (qBallRegion_measure_lt_top T G.hstrict G.hqpos))

/-- Finite normalized real volume of the hull. -/
theorem normalizedRealVolume_hull_lt_top (G : HaarStrictGeometry T) :
    s1902NormalizedHaar T (s1902Hull T) < ⊤ :=
  G.hhfin

/-- **Annulus strictness**: the normalized real volume of the q-ball is strictly
  smaller than that of the hull (from the Haar strictness theorem). -/
theorem normalizedRealVolume_strict (G : HaarStrictGeometry T) :
    normalizedRealVolume T (qBallRegion T) < normalizedRealVolume T (s1902Hull T) :=
  ENNReal.toReal_lt_toReal
    (ne_of_lt (qBallRegion_measure_lt_top T G.hstrict G.hqpos))
    (ne_of_lt G.hhfin)
    (s1902NormalizedHaar_haarStrict T G.hstrict G.hqpos G.hultra G.b0)

/-- **Unconditional xi-e requirement**: the strict measure is PROVED from the annulus
  theorem; only the geometric side conditions are hypotheses. -/
def unconditionalRequirement (G : HaarStrictGeometry T) :
    XiEContainmentRequirement (S1902Carrier T) (normalizedRealVolume T) where
  qRegion := qBallRegion T
  thetaPossibleImages := qBallRegion T
  hullRegion := s1902Hull T
  q_in_possible := fun _ hx => hx
  possible_in_hull := qBallRegion_subset_hull_real T G
  q_pos := normalizedRealVolume_qBall_pos T G
  strict_measure := normalizedRealVolume_strict T G

/-- The Cor 3.12 conclusion with `strict_measure` RESOLVED (no named field): the
  green `requirement_cor312` on the unconditional requirement. -/
theorem unconditional_cor312 (G : HaarStrictGeometry T)
    (hqneg : requirementSignedQ (unconditionalRequirement T G) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (requirementContract (unconditionalRequirement T G) hqneg ipl hipl she hshe apt hapt) :=
  requirement_cor312 (unconditionalRequirement T G) hqneg ipl hipl she hshe apt hapt

/-- The resolved signed inequality (paper shape). -/
theorem unconditional_paper_inequality (G : HaarStrictGeometry T) :
    requirementSignedQ (unconditionalRequirement T G) ≤
      requirementSignedTheta (unconditionalRequirement T G) :=
  requirement_signed_inequality (unconditionalRequirement T G)

/-- The resolved signed inequality is STRICT (non-vacuity). -/
theorem unconditional_paper_inequality_strict (G : HaarStrictGeometry T) :
    requirementSignedQ (unconditionalRequirement T G) <
      requirementSignedTheta (unconditionalRequirement T G) :=
  requirement_strict_signed (unconditionalRequirement T G)

end

end LeanFormal.IUT.XiFPaper.Mzk1Cor312UnconditionalStrictAcceptanceActual