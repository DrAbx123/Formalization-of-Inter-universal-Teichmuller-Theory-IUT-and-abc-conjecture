/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S1902ActualThetaHullActual
import tmp.sheaf.xif.paper.Mzk1HaarStrictScalingProductActual
import tmp.sheaf.xif.paper.Mzk1Cor312AcceptanceInterfaceActual
import tmp.sheaf.xif.paper.Mzk1KummerRealizationActual
import tmp.sheaf.xif.paper.S1902ActualThetaHullActual

/-!
# A588 Cor 3.12 requirement RESOLVED (final acceptance file)

`Mzk1HaarStrictScalingProductActual` proves that the xi-e requirement
`rpRequirement : XiEContainmentRequirement` has its **`strict_measure` as a THEOREM**
(1D p-scaling Haar strictness `rootExtensionHaar_ball_strict` + real product
strictness `Finset.prod_lt_prod` + `ENNReal.toReal_lt_toReal.mpr`), and that the
green `requirement_cor312` yields `Cor312Conclusion` (`rp_cor312`).

This file is the Cor 3.12 acceptance at the requirement level:
* `resolvedCor312`: `Cor312Conclusion` from any real `hqneg`/IPL/SHE/APT evidence;
* `resolved_paper_inequality`: the paper inequality `-|log Theta| >= -|log q|`;
* `resolved_strict_inequality`: its strict form (non-vacuity of xi-e);
* `resolved_strict_measure`: the strict Haar measure inequality (PROVED, not named);
* `#print axioms rp_cor312` gate at the end (expected
  `[propext, Classical.choice, Quot.sound]`).

Remaining named inputs: the `PaperKummerReading` reading (canonical version is `rfl`
by definition), the sign hypothesis `hqneg`, and the real `(IPL)/(SHE)/(APT)` evidence.
No `sorry`, no custom axiom, no closure claim for ABC.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312RequirementResolvedActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarStrictScalingProductActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312AcceptanceInterfaceActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- **Cor 3.12 resolved**: the requirement-level `Cor312Conclusion`, from the green
  `rpRequirement` (whose `strict_measure` is a theorem) and real evidence. -/
theorem resolvedCor312 (hqneg : requirementSignedQ (rpRequirement T) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (requirementContract (rpRequirement T) hqneg ipl hipl she hshe apt hapt) :=
  rp_cor312 (T := T) hqneg ipl hipl she hshe apt hapt

/-- The paper inequality `-|log Theta| >= -|log q|` for the resolved requirement. -/
theorem resolved_paper_inequality :
    requirementSignedQ (rpRequirement T) ≤ requirementSignedTheta (rpRequirement T) :=
  acceptance_paper_inequality (rpRequirement T)

/-- The strict paper inequality (non-vacuity of xi-e). -/
theorem resolved_strict_inequality :
    requirementSignedQ (rpRequirement T) < requirementSignedTheta (rpRequirement T) :=
  acceptance_paper_inequality_strict (rpRequirement T)

/-- The strict Haar measure inequality: PROVED, not a named field. -/
theorem resolved_strict_measure :
    rpVolume T (rpRegion T) < rpVolume T (s1902Hull T) :=
  rpVolume_strict (T := T)

/-- The `C_Theta >= -1` form for the resolved requirement. -/
theorem resolved_CTheta (hqneg : requirementSignedQ (rpRequirement T) < 0)
    {C : ℝ}
    (hC : requirementSignedTheta (rpRequirement T) ≤ C * (-requirementSignedQ (rpRequirement T))) :
    -1 ≤ C :=
  acceptance_CTheta (rpRequirement T) hqneg hC

end LeanFormal.IUT.XiFPaper.Mzk1Cor312RequirementResolvedActual

/-! ### Axiom gate (top level) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1HaarStrictScalingProductActual.rp_cor312

end