/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1Cor312ResolvedStrictAcceptanceActual

/-!
# A551 checks: strict_measure resolution accounting

Machine checks that in the resolved acceptance path:
* `q_pos` is a theorem of the positive-measure q-region (`=1` normalized volume);
* `strict_measure` is a theorem derived from the single Haar strict increase
  (`haarStrict`), not a named field;
* the only remaining named inputs are `haarStrict` and the paper readout;
* the signed paper inequality and its strict form are available.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312StrictMeasureChecksActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.Mzk1PositiveMeasureQRegionProofActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312ResolvedStrictAcceptanceActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open MeasureTheory
open scoped ENNReal BigOperators

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The q-region has PROVED positive product Haar measure. -/
theorem qRegion_haar_pos : 0 < rootExtensionProductHaar T (qRegion T) :=
  qRegion_measure_pos T

/-- The q-region has finite product Haar measure. -/
theorem qRegion_haar_lt_top : rootExtensionProductHaar T (qRegion T) < ⊤ :=
  qRegion_measure_lt_top T

/-- The normalized volume of the q-region is `1` (positivity is a theorem). -/
theorem qNormalizedVolume_qRegion_eq_one :
    qNormalizedVolume T (qRegion T) = 1 := by
  apply qNormalizedVolume_qRegion T
  exact ENNReal.toReal_pos (ne_of_gt (qRegion_measure_pos T))
    (ne_of_lt (qRegion_measure_lt_top T))

/-- `q_pos` of the resolved requirement, via the positive-measure region. -/
theorem resolved_requirement_q_pos (D : PositiveQRegionHaarStrict T) :
    (resolvedRequirement T D).q_pos = D.q_pos :=
  rfl

/-- The strict measure is derived, with `haarStrict` the only comparison input. -/
theorem strict_measure_of_haarStrict (D : PositiveQRegionHaarStrict T) :
    (resolvedRequirement T D).strict_measure = D.strict_measure :=
  rfl

/-- **Accounting**: `q_pos` is a theorem; only `haarStrict` (and the paper readout) is
  named in the resolved requirement. -/
theorem resolution_accounting (D : PositiveQRegionHaarStrict T) :
    (0 < qNormalizedVolume T (qRegion T)) ∧
      (qNormalizedVolume T (qRegion T) < qNormalizedVolume T (s1902Hull T)) ∧
      ((rootExtensionProductHaar T (qRegion T)).toReal <
        (rootExtensionProductHaar T (s1902Hull T)).toReal) :=
  ⟨D.q_pos, D.strict_measure, D.haarStrict⟩

/-- Signed paper inequality from the resolved requirement. -/
theorem resolved_signed_inequality (D : PositiveQRegionHaarStrict T) :
    requirementSignedQ (resolvedRequirement T D) ≤
      requirementSignedTheta (resolvedRequirement T D) :=
  resolved_paper_inequality T D

end

end LeanFormal.IUT.XiFPaper.Mzk1Cor312StrictMeasureChecksActual