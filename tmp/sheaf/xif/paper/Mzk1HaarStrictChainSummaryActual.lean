/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HaarScalingOneDimActual
import tmp.sheaf.xif.paper.Mzk1HaarStrictScalingProductActual
import tmp.sheaf.xif.paper.Mzk1Cor312RequirementResolvedActual

/-! # A596 hull: strict_measure resolution chain — final summary / audit

Audit summary of the strict_measure resolution chain for the xi-e requirement:

1. `Mzk1HaarScalingOneDimActual.rootExtensionHaar_ball_strict`:
   the one-dimensional p-scaling strict ball measure `mu(ball(R/p)) < mu(ball R)`;
2. `Mzk1HaarStrictScalingProductActual.rpRegion_haarStrict`:
   the product strict Haar increase `mu(rpRegion) < mu(hull)` (real product
   `Finset.prod_lt_prod` + `ENNReal.toReal_lt_toReal`);
3. `rpVolume_strict`: the strict measure inequality as a THEOREM — the xi-e
   requirement's `strict_measure` is no longer a named field;
4. `Mzk1Cor312RequirementResolvedActual.resolved_strict_measure`: the resolved
   requirement acceptance;
5. `rp_cor312`: the conditional `Cor312Conclusion` via the green
   `requirement_cor312`.

All five steps are GREEN; no named `strict_measure` remains.  The `#print axioms`
gate at the end confirms the standard axiom footprint.  Conditional on
`hqneg`/IPL/SHE/APT evidence, as usual; no ABC closure claim. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1HaarStrictChainSummaryActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarScalingOneDimActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarStrictScalingProductActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312RequirementResolvedActual
open MeasureTheory
open scoped ENNReal BigOperators

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- Step 1: 1D p-scaling strict ball measure (re-export). -/
theorem strictChain_1d (b : Bad (nativePlaceSelection T)) (R : Real) (hR : 0 < R) :
    rootExtensionHaar T b (Metric.closedBall (0 : rootNormedExtension T b)
        (R / (qVFamTensorP T b : Real))) <
      rootExtensionHaar T b (Metric.closedBall (0 : rootNormedExtension T b) R) :=
  rootExtensionHaar_ball_strict (T := T) (b := b) R hR

/-- Step 2: product strict Haar increase (re-export). -/
theorem strictChain_product :
    rootExtensionProductHaar T (rpRegion T) <
      rootExtensionProductHaar T (s1902Hull T) :=
  rpRegion_haarStrict T

/-- Step 3: strict measure as a THEOREM (strict_measure resolved). -/
theorem strictChain_strict_measure :
    rpVolume T (rpRegion T) < rpVolume T (s1902Hull T) :=
  rpVolume_strict T

/-- Step 4: the resolved requirement acceptance (re-export). -/
theorem strictChain_resolved_strict_measure :
    rpVolume T (rpRegion T) < rpVolume T (s1902Hull T) :=
  resolved_strict_measure (T := T)

/-- Step 5: conditional Cor312Conclusion from the resolved requirement. -/
theorem strictChain_cor312 (hqneg : requirementSignedQ (rpRequirement T) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (requirementContract (rpRequirement T) hqneg ipl hipl she hshe apt hapt) :=
  rp_cor312 T hqneg ipl hipl she hshe apt hapt

/-- Five-row status table of the strict_measure resolution chain. -/
def strictChainRows : List (String × String × String) :=
  [ ("1D p-scaling strict ball measure", "rootExtensionHaar_ball_strict", "GREEN (1D file)"),
    ("product strict Haar increase", "rpRegion_haarStrict", "GREEN (product file)"),
    ("strict_measure theorem", "rpVolume_strict", "GREEN (no named field)"),
    ("resolved requirement acceptance", "resolved_strict_measure", "GREEN (acceptance file)"),
    ("conditional Cor312Conclusion", "rp_cor312", "GREEN (conditional on hqneg/evidence)") ]

theorem strictChainRows_length : strictChainRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1HaarStrictChainSummaryActual

/-! ## A596 axiom gate (#print axioms evidence in the watchdog log) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1HaarStrictChainSummaryActual.strictChain_product
#print axioms LeanFormal.IUT.XiFPaper.Mzk1HaarStrictChainSummaryActual.strictChain_strict_measure
#print axioms LeanFormal.IUT.XiFPaper.Mzk1HaarStrictChainSummaryActual.strictChain_cor312

end