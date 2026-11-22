/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import tmp.sheaf.xif.paper.Mzk1SignedLogVolumeCor312Actual

/-! # A1045: q-region inclusion skeleton (abstract monotonicity of log-volume) -/

/-
| field | value |
|---|---|
| Status | PARTIAL (abstract skeleton; concrete q-pilot/theta regions are FIELD-ASSUMED) |
| DIRECTION-VERIFIED (SUFFICIENT ONLY) | (A1049/A1052) with `logVol := -log mu`:
  (1) `-|log q| = -A`, `-|log Theta| = -R`; (2) the variant `-A <= -R` is equivalent
  (by negating) to `A >= R`; (3) `A = log mu(qRegion)`, `R = log mu(thetaRegion)`, so
  `A >= R` is equivalent to `mu(qRegion) >= mu(thetaRegion)`; (4) measure monotonicity
  gives only the ONE-WAY implication `thetaRegion ⊆ qRegion -> mu(thetaRegion) <= mu(qRegion)`,
  hence `thetaRegion ⊆ qRegion` is a **SUFFICIENT** condition for the variant (not an
  iff; the converse would need a null-set/measurability argument and is not claimed).
  The opposite inclusion gives `-A >= -R`; see `variant_rankone_conditional_rev`. |
| CONVENTION | This file's `logVol := -log mu` with `logVol q = -A` forces `mu q = e^{A}` (a RECIPROCAL/large-volume normalization). The paper-faithful Haar volume has `mu q = e^{-A} < 1`; in that normalization the correct containment is `qPilotRegion subset thetaHullRegion` and the reusable bridge is `Mzk1SignedLogVolumeCor312Actual.signed_cor312_inequality` (see adapter below and `coord/REUSE-SIGNEDLOG-INTEGRATION.md`). Both statements are internally consistent but use different volume normalizations; do NOT mix them. |
| STATUS-EXTRA | `SUPERSEDED-PARTIAL`: the abstract `RegionLogVol`/`haarLogVolume_mono_of_subset` duplicate `Mzk1SignedLogVolumeCor312Actual.signedLogVolume`/`signedLogVolume_mono`; new adapter `cor312_signed_conditional` reuses the signed stack (see `coord/REUSE-SIGNEDLOG-INTEGRATION.md`). |
| GAP | GAP-N5: the two volume identities (`logVol qPilotRegion = -|log q|`,
  `logVol thetaHullRegion = -|log Theta|`) are FIELD-ASSUMED (paper Step (xi-d)). |
| 循环性 | no target is assumed; the monotonicity lemma is pure measure theory. |

This file contains no sorry and no axiom.  It only proves the measure-theoretic monotonicity
of the negative-log volume and the arithmetic consequence of an inclusion + the two volume
identities (both supplied as explicit hypotheses/fields). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1QRegionInclusionActual

open MeasureTheory

/-- Abstract negative-log-volume region data: `logVol S = -log (mu S).toReal`. -/
structure RegionLogVol (α : Type) [MeasurableSpace α] where
  mu : Measure α
  logVol : Set α → Real
  logVol_eq : ∀ S : Set α, logVol S = -Real.log (mu S).toReal

/-- **Monotonicity of negative-log-volume**: `S subset T` gives `logVol T <= logVol S`
(provided `mu S != 0` and `mu T != top`). -/
theorem haarLogVolume_mono_of_subset {α : Type} [MeasurableSpace α]
    (V : RegionLogVol α) {S T : Set α} (hST : S ⊆ T)
    (hS : V.mu S ≠ 0) (hT : V.mu T < ⊤) :
    V.logVol T ≤ V.logVol S := by
  have hS_lt : V.mu S < ⊤ := lt_of_le_of_lt (measure_mono hST) hT
  have hmono : (V.mu S).toReal ≤ (V.mu T).toReal :=
    ENNReal.toReal_mono hT.ne (measure_mono hST)
  have hSpos : 0 < (V.mu S).toReal := ENNReal.toReal_pos hS hS_lt.ne
  have hlog : Real.log (V.mu S).toReal ≤ Real.log (V.mu T).toReal :=
    Real.log_le_log hSpos hmono
  rw [V.logVol_eq T, V.logVol_eq S]
  linarith

/-- Two abstract regions with their volume identities (FIELD-ASSUMED). -/
structure QRegionData (α : Type) [MeasurableSpace α] where
  V : RegionLogVol α
  qRegion : Set α
  thetaRegion : Set α
  absLogQ : Real
  absLogTheta : Real
  vol_q : V.logVol qRegion = -absLogQ
  vol_theta : V.logVol thetaRegion = -absLogTheta
  hq : V.mu qRegion ≠ 0
  htheta : V.mu thetaRegion < ⊤
  htheta_ne : V.mu thetaRegion ≠ 0
  hq_lt : V.mu qRegion < ⊤

/-- **rank-one minimal inclusion (correct direction)**:
`thetaHullRegion subset qPilotRegion` + volume identities imply
`-|log Theta| >= -|log q|` (Cor 3.12 form). -/
theorem rankOne_minimal {α : Type} [MeasurableSpace α] (D : QRegionData α)
    (h : D.thetaRegion ⊆ D.qRegion) :
    -D.absLogTheta ≥ -D.absLogQ := by
  have hvol := haarLogVolume_mono_of_subset D.V h D.htheta_ne D.hq_lt
  rw [D.vol_theta, D.vol_q] at hvol
  linarith

/-- Wrong-direction remark: `qRegion subset thetaRegion` would give the opposite inequality. -/
theorem q_subset_theta_gives_opposite {α : Type} [MeasurableSpace α] (D : QRegionData α)
    (h : D.qRegion ⊆ D.thetaRegion) :
    -D.absLogQ ≥ -D.absLogTheta := by
  have hvol := haarLogVolume_mono_of_subset D.V h D.hq D.htheta
  rw [D.vol_q, D.vol_theta] at hvol
  linarith

/-- Conditional Cor 3.12 (rank-one form): `thetaRegion subset qRegion` plus the two
volume identities give `-|log Theta| >= -|log q|`.  The inclusion is an EXPLICIT
ASSUMPTION (FIELD-ASSUMED); the direction is recorded as DIRECTION-SUFFICIENT above. -/
theorem cor312_rankone_conditional {α : Type} [MeasurableSpace α] (D : QRegionData α)
    (h : D.thetaRegion ⊆ D.qRegion) :
    -D.absLogTheta ≥ -D.absLogQ :=
  rankOne_minimal D h

/-- Signed form: `rhs_theta = -|log Theta|` and `lhs = -|log q|`; the conditional gives
`-A <= rhs_theta`, i.e. the variant inequality in our sign convention. -/
theorem variant_rankone_conditional {α : Type} [MeasurableSpace α] (D : QRegionData α)
    (h : D.thetaRegion ⊆ D.qRegion) :
    -D.absLogQ ≤ -D.absLogTheta :=
  cor312_rankone_conditional D h

/-- If the paper inclusion direction is the opposite one, the same hypotheses give the
opposite inequality; recorded explicitly (reverse direction, not sufficient). -/
theorem variant_rankone_conditional_rev {α : Type} [MeasurableSpace α] (D : QRegionData α)
    (h : D.qRegion ⊆ D.thetaRegion) :
    -D.absLogTheta ≤ -D.absLogQ :=
  q_subset_theta_gives_opposite D h

/-- Rows updated with the conditional form. -/
def qRegionRows2 : List (String × String) :=
  [ ("cor312_rankone_conditional", "theta subset q + volume identities -> -|logTheta| >= -|logq|") ,
    ("variant_rankone_conditional", "-A <= -|logTheta| (variant sign form)") ,
    ("variant_rankone_conditional_rev", "opposite inclusion gives opposite inequality (not sufficient)") ,
    ("inclusion direction", "FIELD-ASSUMED: paper Step (xi-d) direction pending") ]

theorem qRegionRows2_length : qRegionRows2.length = 4 := rfl

def qRegionRows : List (String × String) :=
  [ ("RegionLogVol", "logVol S = -log(mu S).toReal (abstract)") ,
    ("haarLogVolume_mono_of_subset", "S subset T -> logVol T <= logVol S (PROVED)") ,
    ("rankOne_minimal", "theta subset q -> -|logTheta| >= -|logq| (PROVED, abstract)") ,
    ("volume identities", "logVol q = -A, logVol theta = -R (FIELD-ASSUMED, GAP-N5)") ,
    ("DIRECTION-SUFFICIENT", "theta subset q is sufficient; q subset theta gives opposite; converse not claimed") ]

theorem qRegionRows_length : qRegionRows.length = 5 := rfl


/-! ### Adapter: reuse the existing signed-log-volume stack (A1051) -/

open LeanFormal.IUT.XiFPaper.Mzk1SignedLogVolumeCor312Actual

/-- Adapter data: volume function, monotonicity, containment and positivity. -/
structure SignedQRegionData (α : Type*) (vol : Set α → Real) where
  hmono : ∀ {S T : Set α}, S ⊆ T → vol S ≤ vol T
  qRegion : Set α
  hullRegion : Set α
  subset : qRegion ⊆ hullRegion
  q_pos : 0 < vol qRegion

/-- The `XiEContainment` record of the signed stack. -/
def SignedQRegionData.toXiEContainment {α : Type*} {vol : Set α → Real}
    (D : SignedQRegionData α vol) : XiEContainment α vol where
  qRegion := D.qRegion
  hullRegion := D.hullRegion
  subset := D.subset
  q_pos := D.q_pos

/-- **Reused bridge**: `signedQ <= signedTheta` (paper Cor 3.12 signed form). -/
theorem cor312_signed_conditional {α : Type*} {vol : Set α → Real}
    (D : SignedQRegionData α vol) :
    signedQ D.toXiEContainment ≤ signedTheta D.toXiEContainment :=
  signed_cor312_inequality D.hmono D.toXiEContainment

/-- Variant form with the two identifications `signedQ = -A`, `signedTheta = -R`. -/
theorem variant_signed_conditional {α : Type*} {vol : Set α → Real}
    (D : SignedQRegionData α vol) {A R : Real}
    (hA : signedQ D.toXiEContainment = -A)
    (hR : signedTheta D.toXiEContainment = -R) :
    -A ≤ -R := by
  rw [← hA, ← hR]
  exact cor312_signed_conditional D

/-- Paper-faithful signed form: with `vol` the actual (Haar) volume and
`signedQ = -A`, `signedTheta = -R`, the signed containment `qRegion subset hullRegion`
gives the variant `-A <= -R` directly. -/
theorem variant_of_signedContainment {α : Type*} {vol : Set α → Real}
    (D : SignedQRegionData α vol) {A R : Real}
    (hA : signedQ D.toXiEContainment = -A)
    (hR : signedTheta D.toXiEContainment = -R) :
    -A ≤ -R := by
  rw [← hA, ← hR]
  exact cor312_signed_conditional D
def signedIntegrationRows : List (String × String) :=
  [ ("cor312_signed_conditional", "reuses Mzk1SignedLogVolumeCor312Actual.signed_cor312_inequality") ,
    ("variant_signed_conditional", "-A <= -R from the signed bridge + identifications") ,
    ("superseded", "abstract RegionLogVol/haarLogVolume_mono_of_subset kept for reference") ]

theorem signedIntegrationRows_length : signedIntegrationRows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1QRegionInclusionActual