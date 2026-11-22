/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S2708MultiPlaceQPilotActual
import tmp.sheaf.xif.paper.S2717StageAMultiQActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36ProductFormula
import Mathlib.Tactic

/-! # R29q / task-97: q-side bridge between Example36 degree and q-pilot log-volume -/

/-
| field | value |
|---|---|
| Status | PARTIAL (q side): exact q-pilot volume identity and conditional bridge to Example36 degree; the identification `globalPrimeStripWeight d = sourceBadQAbsLog` is an explicit GAP |
| Reuse | `S2708MultiPlaceQPilotActual:146/153/161` (paperQPilotLogVolume_multi and identity to source signed log); `S2717StageAMultiQActual:102/169/190/206/212` (qProduct, qProduct_log, qProduct_abs_log, stageAQParameterSigned_multi); `Example36ProductFormula:313/327/387` (degree, AddMonoidHom, principal unit) |
| GAP | GAP-DEGREE-BRIDGE-Q: a place map `badPlaces -> HeightOneSpectrum (O_F)` with `|log q_b| = nu_v * log #(O_F/v)` is NOT constructed; `QPilotDegreeBridge` is that explicit hypothesis |
| GAP | GAP-S2717-BRIDGE: `S2717QPilotLogVolume` is defined via `S2711I`'s initial source; linking to the present generic `I` needs the S2711-initial identification (not constructed) |
| 纪律 | no sorry/axiom; the conditional bridge is a real theorem with the identification as an explicit hypothesis |
-/

noncomputable section
open scoped BigOperators NumberField
open IsDedekindDomain NumberField

namespace LeanFormal.IUT.XiFPaper.Mzk1DegreeBridgeActual

open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.PrimeStripProductFormula
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S2717StageAMultiQActual

universe ua uv upi umon ui u

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {F : Type u} [Field F] [NumberField F]

local instance badPlacesFintype : Fintype I.initial.badPlaces := I.initial.bad_finite

/-! ## 1. q-side exact identities (re-export) -/

/-- The multi-place q-pilot log-volume is the actual source signed q-pilot log.
Re-export of `S2708MultiPlaceQPilotActual:153`. -/
theorem paperQPilotLogVolume_multi_eq_sourceSigned (D : MultiPlaceQPilotDonor I) :
    paperQPilotLogVolume_multi D = sourceQPilotSignedLog I.initial := by
  exact paperQPilotLogVolume_multi_eq_sourceQPilotSignedLog D

/-- The multi-place q-pilot log-volume is minus the source bad-q absolute log.
Re-export of `S2708MultiPlaceQPilotActual:161`. -/
theorem paperQPilotLogVolume_multi_eq_neg_badQ (D : MultiPlaceQPilotDonor I) :
    paperQPilotLogVolume_multi D = -sourceBadQAbsLog I.initial := by
  exact paperQPilotLogVolume_multi_eq_neg_sourceBadQAbsLog D

/-- The multi-q Stage A endpoint equals the paper q-pilot log-volume.
Re-export of `S2717StageAMultiQActual:212`. -/
theorem stageAQParameterSigned_multi_eq_volume (D : MultiPlaceQPilotDonor I) :
    stageAQParameterSigned_multi D = paperQPilotLogVolume_multi D := by
  exact stageAQParameterSigned_multi_eq D

/-- The product-formula side: the q-product has log equal to the plain (signed) sum of the
per-place logarithms.  Re-export of `S2717StageAMultiQActual:169`. -/
theorem qProduct_log_eq_sum (D : MultiPlaceQPilotDonor I) :
    Real.log (qProduct D) =
      ∑ b : I.initial.badPlaces, Real.log |D.qFamily b| := by
  exact qProduct_log D

/-- **qProduct bridge**: the q-pilot volume is `-|log (qProduct D)|`.
Re-export of `S2717StageAMultiQActual:190`. -/
theorem paperQPilotLogVolume_multi_eq_neg_abs_qProduct_log
    (D : MultiPlaceQPilotDonor I) :
    -|Real.log (qProduct D)| = paperQPilotLogVolume_multi D := by
  exact qProduct_abs_log D

/-! ## 2. The degree bridge (explicit identification as hypothesis) -/

/-- The exact q-side identification needed for the degree bridge: the Example36
explicit-divisor degree of `d` equals the source bad-q absolute-log sum.

Construction of `d` from `badPlaces` (place map + valuations) is the GAP;
this predicate is the honest interface for that identification. -/
def QPilotDegreeBridge (d : SourceModelBackend.ExplicitDivisor F) : Prop :=
  globalPrimeStripWeight (F := F) d = sourceBadQAbsLog I.initial

/-- **Conditional degree bridge (q side).**  If the explicit divisor degree equals the
source bad-q absolute log, then the q-pilot log-volume is minus that degree. -/
theorem paperQPilotLogVolume_multi_eq_neg_degree
    (D : MultiPlaceQPilotDonor I) {d : SourceModelBackend.ExplicitDivisor F}
    (h : QPilotDegreeBridge (I := I) (F := F) d) :
    paperQPilotLogVolume_multi D = -globalPrimeStripWeight (F := F) d := by
  rw [paperQPilotLogVolume_multi_eq_neg_badQ D, ← h]

/-- The source signed q-pilot log is minus the explicit degree under the same bridge. -/
theorem sourceQPilotSignedLog_eq_neg_degree
    {d : SourceModelBackend.ExplicitDivisor F}
    (h : QPilotDegreeBridge (I := I) (F := F) d) :
    sourceQPilotSignedLog I.initial = -globalPrimeStripWeight (F := F) d := by
  rw [← paperQPilotLogVolume_multi_eq_sourceSigned (I := I)
    (D := MultiPlaceQPilotDonor.ofSource (I := I))]
  exact paperQPilotLogVolume_multi_eq_neg_degree (I := I)
    (MultiPlaceQPilotDonor.ofSource (I := I)) h

/-- **Product-formula consistency**: if the divisor `d` is a principal divisor of a global
unit and satisfies the q-side bridge, then the source bad-q absolute log vanishes. -/
theorem sourceBadQAbsLog_eq_zero_of_principal
    {d : SourceModelBackend.ExplicitDivisor F}
    (h : QPilotDegreeBridge (I := I) (F := F) d) (f : Fˣ)
    (hd : d = SourceModelBackend.principalDivisorExplicit (F := F) (Additive.ofMul f)) :
    sourceBadQAbsLog I.initial = 0 := by
  rw [← h, hd]
  exact globalPrimeStripWeight_principalDivisorExplicit (F := F) f

def degreeBridgeRows : List (String × String) :=
  [ ("paperQPilotLogVolume_multi_eq_sourceSigned", "re-export S2708:153") ,
    ("paperQPilotLogVolume_multi_eq_neg_badQ", "re-export S2708:161") ,
    ("stageAQParameterSigned_multi_eq_volume", "re-export S2717StageA:212") ,
    ("qProduct_log_eq_sum", "re-export S2717StageA:169") ,
    ("paperQPilotLogVolume_multi_eq_neg_abs_qProduct_log", "re-export S2717StageA:190") ,
    ("QPilotDegreeBridge", "explicit degree = sourceBadQAbsLog (GAP identification)") ,
    ("paperQPilotLogVolume_multi_eq_neg_degree", "q-pilot volume = -degree (PROVED, conditional)") ,
    ("sourceQPilotSignedLog_eq_neg_degree", "signed q log = -degree (PROVED, conditional)") ,
    ("sourceBadQAbsLog_eq_zero_of_principal", "product formula consistency (PROVED, conditional)") ,
    ("GAP-DEGREE-BRIDGE-Q", "place map badPlaces -> HeightOneSpectrum and valuations missing") ,
    ("GAP-S2717-BRIDGE", "S2711I initial identification missing") ]

theorem degreeBridgeRows_length : degreeBridgeRows.length = 11 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1DegreeBridgeActual