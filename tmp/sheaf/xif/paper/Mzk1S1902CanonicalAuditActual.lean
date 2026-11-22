/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1S1902IQHullInterfaceCanonicalActual
import tmp.sheaf.xif.paper.Mzk1S1902IQHullInterfaceActual
import tmp.sheaf.xif.paper.Mzk1HaarStrictChainSummaryActual
import tmp.sheaf.xif.paper.Mzk1Cor312RequirementResolvedActual
import tmp.sheaf.xif.paper.Mzk1HqnegHullModelActual
import tmp.sheaf.xif.paper.Mzk1FinalConditionalCertificateActual

/-! # A618/A620 hull: mechanized audit of the S1902 canonical chain

One-file audit gate for the canonical S1902/Cor312 artifacts owned or
consumed by the hull lane.  Each `#print axioms` below must show only
`[propext, Classical.choice, Quot.sound]` (no `sorryAx`, no custom axiom).

Artifacts:
* `Mzk1S1902IQHullInterfaceCanonicalActual`: canonical concrete
  `IQHullLogVolumeInterface` re-export (thin);
* `Mzk1S1902IQHullInterfaceActual`: direct concrete instantiation (green);
* `Mzk1HaarStrictChainSummaryActual`: strict_measure resolution summary;
* `Mzk1Cor312RequirementResolvedActual`: resolved xi-e requirement;
* `Mzk1HqnegHullModelActual`: concrete hull-side model discharging `hqneg`;
* `Mzk1FinalConditionalCertificateActual`: final conditional certificate
  (`final_3_12`, `final_abc_of_twoEstimates`, `final_abc_of_bridge`).

ABC gate NOT passed: the two IUT IV Thm 1.10 estimates and the bridge
interface remain explicit hypotheses. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1S1902CanonicalAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1S1902IQHullInterfaceCanonicalActual
open LeanFormal.IUT.XiFPaper.Mzk1S1902IQHullInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarStrictChainSummaryActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312RequirementResolvedActual
open LeanFormal.IUT.XiFPaper.Mzk1HqnegHullModelActual
open LeanFormal.IUT.XiFPaper.Mzk1FinalConditionalCertificateActual
open scoped ENNReal BigOperators

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- Audit: canonical S1902 `IQHullLogVolumeInterface` is the actual paper object. -/
theorem canonicalAudit_interface :
    (s1902IQHullInterfaceCanonical T).hull = s1902Hull T :=
  canonical_hull (T := T)

/-- Audit table of the canonical chain. -/
def canonicalAuditRows : List (String × String × String) :=
  [ ("canonical S1902 IQ hull interface", "s1902IQHullInterfaceCanonical", "GREEN"),
    ("direct S1902 instantiation", "s1902IQHullInterface", "GREEN"),
    ("strict_measure resolution", "strictChain_strict_measure", "GREEN (theorem)"),
    ("resolved requirement", "resolvedCor312", "GREEN (conditional on hqneg/evidence)"),
    ("hqneg hull model", "canonicalHqneg", "GREEN"),
    ("final certificate", "final_3_12 / final_abc_of_twoEstimates", "GREEN (conditional; ABC gate NOT passed)") ]

theorem canonicalAuditRows_length : canonicalAuditRows.length = 6 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1S1902CanonicalAuditActual

end

/-! ### A618 mechanized axiom gate (top level) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1S1902IQHullInterfaceCanonicalActual.s1902IQHullInterfaceCanonical
#print axioms LeanFormal.IUT.XiFPaper.Mzk1S1902IQHullInterfaceActual.s1902IQHull_hull_logVolume_lt_top
#print axioms LeanFormal.IUT.XiFPaper.Mzk1HaarStrictChainSummaryActual.strictChain_strict_measure
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Cor312RequirementResolvedActual.resolvedCor312
#print axioms LeanFormal.IUT.XiFPaper.Mzk1HqnegHullModelActual.canonicalHqneg
#print axioms LeanFormal.IUT.XiFPaper.Mzk1FinalConditionalCertificateActual.final_3_12
#print axioms LeanFormal.IUT.XiFPaper.Mzk1FinalConditionalCertificateActual.final_abc_of_twoEstimates