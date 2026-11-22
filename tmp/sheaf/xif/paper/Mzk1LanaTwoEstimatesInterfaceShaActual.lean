import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesShaActual
import tmp.sheaf.xif.paper.Mzk1LanaIutIVLocalEstimateConsumerActual
import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesReductionShaActual
import Mathlib.Tactic

/-!
# shehdd A652 LANA LocalEstimate <-> ABCTwoEstimates interface equivalence (Sha)

Real content (no gap claimed): the LANA/ported `LocalEstimate` gap interface and
our `ABCTwoEstimates` have the same two-field gap shape, with explicit
conversions in BOTH directions:
* `ABCTwoEstimates -> LocalEstimate E.logVolume E.hullVolume`;
* `LocalEstimate logVolume hullVolume -> ABCTwoEstimates` (existing `toTwoEstimates`);
* both roundtrips are `rfl`;
* `ABCTwoEstimatesReductions` (pointwise height + additive volume) refines the
  LANA local-estimate interface, hence yields `ABCConjecture` through it.

Named inputs (Gap1/Gap2) remain explicit hypotheses; ABC gate NOT passed.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1LanaTwoEstimatesInterfaceShaActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5ABCFormActual
open LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5NumericalActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesShaActual
open LeanFormal.IUT.XiFPaper.Mzk1LanaIutIVLocalEstimateConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesReductionShaActual
open LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesHeightLemmasShaActual

/-- `ABCTwoEstimates` gives the LANA `LocalEstimate` with the SAME volume data. -/
def twoEstimatesToLocalEstimate (E : ABCTwoEstimates) :
    LocalEstimate E.logVolume E.hullVolume :=
  { height_estimate := E.height_estimate
    volume_estimate := E.volume_estimate }

/-- Roundtrip `ABCTwoEstimates -> LocalEstimate -> ABCTwoEstimates` is the identity. -/
theorem twoEstimates_toLocal_toTwo (E : ABCTwoEstimates) :
    (twoEstimatesToLocalEstimate E).toTwoEstimates = E :=
  rfl

/-- Roundtrip `LocalEstimate -> ABCTwoEstimates -> LocalEstimate` is the identity. -/
theorem localEstimate_toTwo_toLocal {logVolume : Nat → Nat → Nat → Real}
    {hullVolume : Real} (L : LocalEstimate logVolume hullVolume) :
    twoEstimatesToLocalEstimate L.toTwoEstimates = L :=
  rfl

/-- Pointwise reductions refine the LANA local-estimate interface. -/
theorem reductionsToLocalEstimate (R : ABCTwoEstimatesReductions) :
    LocalEstimate R.logVolume R.hullVolume where
  height_estimate := by
    intro δ hδ a b c htriple
    exact height_estimate_of_weight_bound (R.logVolume_nonneg a b c) hδ
      (R.height_pointwise a b c htriple)
  volume_estimate := by
    intro δ hδ
    refine ⟨R.D0, fun a b c htriple => ?_⟩
    have hw : 0 ≤ arithmeticWeight (abcRationalPoint a c) :=
      arithmeticWeight_nonneg_local (abcRationalPoint a c)
    have h1 := R.volume_additive a b c htriple
    nlinarith

/-- Green consumer: the pointwise reductions imply `ABCConjecture` through the
LANA local-estimate interface. -/
theorem abc_of_reductions_via_localEstimate (R : ABCTwoEstimatesReductions) :
    ABCConjecture :=
  abc_of_localEstimate (reductionsToLocalEstimate R)

/-- Green consumer: a two-estimate package implies ABC through the LANA interface. -/
theorem abc_of_twoEstimates_via_localEstimate (E : ABCTwoEstimates) : ABCConjecture :=
  abc_of_localEstimate (twoEstimatesToLocalEstimate E)

end LeanFormal.IUT.XiFPaper.Mzk1LanaTwoEstimatesInterfaceShaActual

/-! ### Axiom gates -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1LanaTwoEstimatesInterfaceShaActual.twoEstimates_toLocal_toTwo
#print axioms LeanFormal.IUT.XiFPaper.Mzk1LanaTwoEstimatesInterfaceShaActual.abc_of_reductions_via_localEstimate
#print axioms LeanFormal.IUT.XiFPaper.Mzk1LanaTwoEstimatesInterfaceShaActual.abc_of_twoEstimates_via_localEstimate
