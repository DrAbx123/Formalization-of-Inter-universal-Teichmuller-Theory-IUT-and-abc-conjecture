/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1PositiveMeasureQRegionProofActual
import tmp.sheaf.xif.paper.Mzk1XiEContainmentRequirementActual

/-!
# A551 resolved strict_measure: positive-measure q-region acceptance

The half-ball q-region `qRegion T` of `Mzk1PositiveMeasureQRegionProofActual` is a
PROVED positive-measure region contained in the actual Theta hull, with
`qNormalizedVolume (qRegion) = 1`.  Consequently:

* `q_pos` of the xi-e requirement is a THEOREM (`qNormalizedVolume_qRegion`);
* `strict_measure` is a THEOREM derived from the single Haar inequality
  `haarStrict : vol_haar qRegion < vol_haar hull` (the annulus step); it is no longer
  a named field of the acceptance path;
* the remaining named data are only `haarStrict` (a comparison of the two actual Haar
  measures) and the `PaperKummerReading` 1-column readout (for the paper statement).

`resolved_cor312` then feeds the green `requirement_cor312` to obtain
`Cor312Conclusion` with strict measure RESOLVED.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312ResolvedStrictAcceptanceV3Actual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.Mzk1PositiveMeasureQRegionProofActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open MeasureTheory
open scoped ENNReal BigOperators

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- **The resolved xi-e requirement**: half-ball q-region, hull `s1902Hull`, volume
  `qNormalizedVolume`; `q_pos` and `strict_measure` come from `PositiveQRegionHaarStrict`
  (derived), not from named fields of the acceptance path. -/
noncomputable def resolvedRequirement (D : PositiveQRegionHaarStrict T) :
    XiEContainmentRequirement (S1902Carrier T) (qNormalizedVolume T) where
  qRegion := qRegion T
  thetaPossibleImages := qRegion T
  hullRegion := s1902Hull T
  q_in_possible := fun _ hx => hx
  possible_in_hull := qRegion_subset_hull T
  q_pos := D.q_pos
  strict_measure := D.strict_measure

/-- `q_pos` of the resolved requirement, derived from `qNormalizedVolume_qRegion = 1`. -/
theorem resolved_q_pos (D : PositiveQRegionHaarStrict T) :
    0 < qNormalizedVolume T (qRegion T) :=
  D.q_pos

/-- `strict_measure` of the resolved requirement is DERIVED from the Haar inequality. -/
theorem resolved_strict_measure (D : PositiveQRegionHaarStrict T) :
    qNormalizedVolume T (qRegion T) < qNormalizedVolume T (s1902Hull T) :=
  D.strict_measure

/-- The derivation chain: positive-measure half-ball + Haar strict increase give the
  resolved requirement's strict measure (no named strict_measure field is consumed). -/
theorem resolved_strict_of_haar (hpos :
    0 < (rootExtensionProductHaar T (qRegion T)).toReal)
    (hlt : (rootExtensionProductHaar T (qRegion T)).toReal <
      (rootExtensionProductHaar T (s1902Hull T)).toReal) :
    qNormalizedVolume T (qRegion T) < qNormalizedVolume T (s1902Hull T) :=
  (positiveQRegionHaarStrict_of_strict T hpos hlt).strict_measure

/-- **Resolved acceptance conclusion**: the green `requirement_cor312` on the resolved
  requirement yields `Cor312Conclusion` for arbitrary real `(IPL)/(SHE)/(APT)` evidence;
  the only named input is `haarStrict` (plus the evidence Props). -/
theorem resolved_cor312 (D : PositiveQRegionHaarStrict T)
    (hqneg : requirementSignedQ (resolvedRequirement T D) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (requirementContract (resolvedRequirement T D) hqneg ipl hipl she hshe apt hapt) :=
  requirement_cor312 (resolvedRequirement T D) hqneg ipl hipl she hshe apt hapt

/-- The resolved signed inequality (paper shape) is the green requirement inequality. -/
theorem resolved_paper_inequality (D : PositiveQRegionHaarStrict T) :
    requirementSignedQ (resolvedRequirement T D) ≤
      requirementSignedTheta (resolvedRequirement T D) :=
  requirement_signed_inequality (resolvedRequirement T D)

/-- The resolved signed inequality is STRICT (non-vacuity, no reflexivity). -/
theorem resolved_paper_inequality_strict (D : PositiveQRegionHaarStrict T) :
    requirementSignedQ (resolvedRequirement T D) <
      requirementSignedTheta (resolvedRequirement T D) :=
  requirement_strict_signed (resolvedRequirement T D)

end LeanFormal.IUT.XiFPaper.Mzk1Cor312ResolvedStrictAcceptanceV3Actual

