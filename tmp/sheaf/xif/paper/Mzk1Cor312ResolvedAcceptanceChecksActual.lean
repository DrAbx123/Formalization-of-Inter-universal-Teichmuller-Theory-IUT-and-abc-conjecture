/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1Cor312AcceptanceResolvedV2Actual

/-!
# A561 checks: strict-measure-resolved acceptance accounting

Machine checks that in the resolved acceptance artifact:
* `strict_measure` is the proved p-scaling theorem;
* the annulus has positive measure (theorem);
* the remaining assumptions are only nonemptiness/`hqneg`/IPL-SHE-APT evidence.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312ResolvedAcceptanceChecksActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarStrictScalingActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarStrictRPConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312AcceptanceResolvedV2Actual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open scoped BigOperators

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- `strict_measure` of the resolved requirement equals the proved p-scaling theorem. -/
theorem strict_measure_is_scaling_theorem :
    (rpRequirement T).strict_measure = rp_strict_measure_resolved T :=
  rfl

/-- Accounting: both non-vacuity facts are theorems; only geometric/evidence inputs remain. -/
theorem resolved_accounting :
    (rpVolume T (rpRegion T) < rpVolume T (s1902Hull T)) ∧
      (0 < rootExtensionProductHaar T (s1902Hull T \ rpRegion T)) :=
  ⟨resolved_strict_measure_theorem T, resolved_annulus_positive T⟩

/-- The resolved signed strict inequality. -/
theorem resolved_signed_strict :
    requirementSignedQ (rpRequirement T) < requirementSignedTheta (rpRequirement T) :=
  resolved_paper_inequality_strict T

end

end LeanFormal.IUT.XiFPaper.Mzk1Cor312ResolvedAcceptanceChecksActual