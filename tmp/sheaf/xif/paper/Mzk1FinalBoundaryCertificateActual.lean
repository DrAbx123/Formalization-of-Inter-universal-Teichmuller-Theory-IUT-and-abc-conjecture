/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1FinalConditionalCertificateActual
import tmp.sheaf.xif.paper.Mzk1GapTightnessActual
import tmp.sheaf.xif.paper.Mzk1PaperRegionNecessityFinalActual
import tmp.sheaf.xif.paper.Mzk1LanaBridgeAuditActual

/-!
# A647 FINAL BOUNDARY CERTIFICATE (mainline)

One final boundary certificate, as a single conjunction:
(a) `final_3_12`: the resolved requirement (whose `strict_measure` is a THEOREM)
    yields `Cor312Conclusion` from real `hqneg`/IPL/SHE/APT evidence;
(b) `paperGap_boundary_calibrated`: `Nonempty Cor312ToABCBridgeInterface.{0} ↔
    ABCConjecture` (green calibration);
(c) `paperGap_named_fields_tight`: the two named gap shapes imply `ABCConjecture`;
(d) `paperRegionNecessityFinal`: the region-necessity audit conjunction;
(e) scope: ABC gate NOT passed; no canonical object changed.

The retired `Mzk1A618MachineProofActual` is NOT imported; the canonical A618 machine
proof is `Mzk1A618ScalingObstructionActual.identity_scaleShift_obstruction` (trio).

This is a boundary certificate, NOT a proof of ABC. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1FinalBoundaryCertificateActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarStrictScalingProductActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1FinalConditionalCertificateActual
open LeanFormal.IUT.XiFPaper.Mzk1GapTightnessActual
open Mzk1LanaBridgeAuditActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperRegionNecessityFinalActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- **Final boundary certificate (a)-(e)** as a single conjunction. -/
theorem finalBoundaryCertificate
    (point : Nat → Nat → Nat → S1902Carrier T) (epsilon : ℝ)
    {X : Type*} (W : IQHullLogVolumeInterface X)
    (region : Nat → Nat → Nat → Set X)
    (hfin : W.logVolume W.hull < ⊤)
    (hsub : ∀ a b c : Nat, IsABCTriple a b c → region a b c ⊆ W.hull)
    (hqneg : requirementSignedQ (rpRequirement T) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    (Cor312Conclusion
      (requirementContract (rpRequirement T) hqneg ipl hipl she hshe apt hapt)) ∧
      (Nonempty Cor312ToABCBridgeInterface.{0} ↔ ABCConjecture) ∧
      ((Gap1Prop (s1902IQHullLogVolumeInterface T)
          (paperComparisonRegion T point) ∧
        Gap2Prop (s1902IQHullLogVolumeInterface T)
          (paperComparisonRegion T point)) → ABCConjecture) ∧
      (PaperRegionNecessityFinalClaim T point epsilon W region hfin hsub) ∧
      (scopeRecord.length = 3) :=
  ⟨final_3_12 (T := T) hqneg ipl hipl she hshe apt hapt,
   paperGap_boundary_calibrated,
   fun h => paperGap_named_fields_tight T point h.1 h.2,
   paperRegionNecessityFinal T point epsilon W region hfin hsub,
   scopeRecord_length⟩

end LeanFormal.IUT.XiFPaper.Mzk1FinalBoundaryCertificateActual

end

/-! ### Axiom gates (top level) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1FinalBoundaryCertificateActual.finalBoundaryCertificate