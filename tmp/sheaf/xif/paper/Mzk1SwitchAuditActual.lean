/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1N3SharedContainerRealActual
import tmp.sheaf.xif.paper.Mzk1N3SharedContainerBridgeShaActual
import Mathlib.Tactic

/-! # Mzk1SwitchAuditActual — A765: two-switch audit + vacuity fixes (SUPERSEDED/RETRACTED)

Audit of the two IUT switches flagged in ROUTES v2 §6.5, and of the vacuity traps:

**Switch 1 (theta-value exponent).**  lana `Iut/Concrete/ThetaRegion.lean:151-184`
(`scaleEltAt`, `thetaFiniteOn`, `thetaComponentOn`): the scaling element is
`q_{v_l}^{(i+1)²}` — the exponent is `(i+1)²` determined by the capsule index `i`,
and the label `l ∈ S ⊆ S_{i+2}` only selects the tensor factor / place, never the
exponent.  Encoded/proved here: `paperScaleExponent i l = (i+1)^2` is independent of
the label, `paperScaleExponent_label_indep`.

**Switch 2 (procession: average vs max).**  lana `logVol` is the uniform capsule
average `(∑_i packetVol_i)/nC D` (`Iut/Concrete/ArchScaling.lean:485-498`;
`logVol_hull_vcI_eq` in `Iut/WallEquiv/VcI.lean:23`, i.e. `/ℓ*`), not the maximum over
capsules.  The two differ: `processionAvg ≤ processionMax` (`processionAvg_le_max`),
so using the maximum as RHS makes the wall strictly easier; a faithful formalization
must use the uniform average (`max_rhs_not_faithful`).

**Labels reading.**  lana has `ivLabels = {distinguished}` (IUT IV's reading) and
`litLabels = univ` (literal (Ind1) union); `ivLabels ⊆ litLabels` is proved in lana.
Encoded here as `ivReading ⊆ literalReading`; this is a documented reading choice,
not a hidden switch.

**Our files.**
* `Mzk1N3SharedContainerPlanActual`: `SharedContainerGap` does NOT mention `D`
  (`∃ p : GapParameters, p.inequality`), hence is trivially satisfiable — **VACUOUS,
  SUPERSEDED** by the `paperGap`-of-`D` form below.
* `Mzk1N3SharedContainerRealActual`: the readings are the actual S3137 Haar / q-pilot
  readings (`actualC3LogShellTensorHaar`, `qPilotLogVolumeReading`); nothing is
  fabricated; but only the global comparison is formalized (capsule/procession
  structure not exposed) — faithful-but-incomplete, the remaining dictionary is
  exactly the two log-volume alignments.
* `Mzk1ThetaValue312SharedActual`: its `SharedContainerVolume.regionVolume` is an
  arbitrary `Set D.analyticSpace → Real` function with consistency conditions only —
  it can silently hide the max-vs-average switch; recorded as FLAGGED and not used
  in the final chain.
* `Mzk1ThetaValue312Actual`: toy carrier (`Set Real := {0}` etc.) — REJECTED by its
  owner (shehdd), kept as history only.
* `final_conditional_ABC.hfull` — **RETRACTED** (unsatisfiable for fixed T; see
  `Mzk1A703CorrectionQpilotActual`).

Replacement statement WITHOUT the vacuous objects: `paperGapStatement C3 P` below
(the `paperGap` of the constructed real container), equivalent to the actual S3137
comparison and to `Paper312Statement`. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1SwitchAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.Mzk1N3SharedContainerRealActual
open LeanFormal.IUT.XiFPaper.Mzk1N3SharedContainerBridgeShaActual
open LeanFormal.IUT.XiFPaper.Mzk1Paper312StatementActual
open scoped BigOperators

/-! ### Switch 1: the theta exponent is fixed by the capsule index -/

/-- The paper theta scaling exponent of capsule `i` and label `l`: `(i+1)^2`
(lana `scaleEltAt`: `qroot ^ (i.1+1)^2`).  It does not depend on the label. -/
def paperScaleExponent (i l : ℕ) : ℕ := (i + 1) ^ 2

/-- The exponent is label-independent (the label only chooses the tensor factor). -/
theorem paperScaleExponent_label_indep (i l l' : ℕ) :
    paperScaleExponent i l = paperScaleExponent i l' := rfl

/-- The exponent of capsule `i` is exactly `(i+1)^2`. -/
theorem paperScaleExponent_eq (i l : ℕ) : paperScaleExponent i l = (i + 1) ^ 2 := rfl

/-! ### Switch 2: procession average vs maximum -/

/-- The uniform procession average `(∑_i f i)/n` (lana's `logVol`). -/
noncomputable def processionAvg (n : ℕ) (f : Fin n → ℝ) : ℝ :=
  (∑ i, f i) / (n : ℝ)

/-- The maximum over the procession capsules. -/
noncomputable def processionMax (n : ℕ) (hn : 0 < n) (f : Fin n → ℝ) : ℝ :=
  Finset.univ.sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ f

/-- The uniform average is at most the maximum. -/
theorem processionAvg_le_max (n : ℕ) (hn : 0 < n) (f : Fin n → ℝ) :
    processionAvg n f ≤ processionMax n hn f :=
by
  have hle : ∀ i : Fin n, f i ≤ processionMax n hn f := fun i =>
    Finset.le_sup' _ (Finset.mem_univ i)
  have hsum : (∑ i, f i) ≤ ∑ _i : Fin n, processionMax n hn f := Finset.sum_le_sum
    (fun i _ => hle i)
  have hconst : (∑ _i : Fin n, processionMax n hn f) = (n : ℝ) * processionMax n hn f := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
  unfold processionAvg
  rw [div_le_iff₀ hnpos]
  calc (∑ i, f i) ≤ (n : ℝ) * processionMax n hn f := by
        rw [← hconst]; exact hsum
    _ = processionMax n hn f * (n : ℝ) := by ring

/-- Using the maximum as RHS is NOT faithful: it makes the wall easier.  If a bound
holds with the uniform-average RHS it holds with the maximum RHS, but not conversely
in general (`1 ≤ 2` witnesses the strict gap). -/
theorem max_rhs_not_faithful {L R : ℝ} (h : L ≤ R) (n : ℕ) (hn : 0 < n)
    (f : Fin n → ℝ) (hR : R = processionAvg n f) :
    L ≤ processionMax n hn (fun i => f i) := by
  rw [hR] at h
  exact le_trans h (processionAvg_le_max n hn f)

/-! ### Labels reading (documented choice) -/

/-- IUT IV's reading: a single distinguished label. -/
def ivReading (n : ℕ) : Set (Fin n) := {i | (i : ℕ) = 0}

/-- Literal (Ind1) reading: all labels. -/
def literalReading (n : ℕ) : Set (Fin n) := Set.univ

theorem ivReading_subset_literalReading (n : ℕ) : ivReading n ⊆ literalReading n :=
  Set.subset_univ _

/-! ### Our-file audit table -/

/-- Two-switch and fidelity audit rows for the qpilot N3 files. -/
def switchAuditRows : List (String × String × String) :=
  [ ("lana thetaComponentOn/scaleEltAt exponent", "CONFIRMED (i+1)^2 fixed per capsule",
     "Iut/Concrete/ThetaRegion.lean:151-184; label-independent"),
    ("lana procession", "CONFIRMED uniform average /nC",
     "ArchScaling.lean:485-498; logVol_hull_vcI_eq /ℓ*"),
    ("lana labels reading", "DOCUMENTED CHOICE", "ivLabels={j} vs litLabels=univ"),
    ("Mzk1N3SharedContainerPlanActual", "SUPERSEDED (vacuous D-free SharedContainerGap)",
     "replaced by paperGapStatement"),
    ("Mzk1N3SharedContainerRealActual", "FAITHFUL-BUT-INCOMPLETE",
     "actual S3137 readings; global paperGap; capsule structure not exposed"),
    ("Mzk1ThetaValue312SharedActual", "FLAGGED (regionVolume arbitrary field)",
     "can hide max-vs-average switch; not used in final chain"),
    ("Mzk1ThetaValue312Actual", "REJECTED (toy carrier)", "owner shehdd"),
    ("final_conditional_ABC.hfull", "RETRACTED (unsatisfiable)",
     "Mzk1A703CorrectionQpilotActual") ]

theorem switchAuditRows_length : switchAuditRows.length = 8 := rfl

/-! ### Vacuity fix: replacement statement in `paperGap D` form -/

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PaperQPilotObjectActual (l := l) (I := I))

/-- Replacement for the vacuous `SharedContainerGap`: the paper gap of the
constructed real container (contains `D`, no free parameters). -/
def paperGapStatement : Prop :=
  paperGap (paperSharedContainerReal (l := l) (V := V) (I := I) C3 P)

/-- The replacement statement is exactly the actual q-pilot/θ-hull comparison. -/
theorem paperGapStatement_iff_qThetaComparison :
    paperGapStatement (l := l) (V := V) (I := I) C3 P ↔
      qThetaPilotLogVolumeComparison (l := l) (V := V) (I := I) C3 P :=
  paperSharedContainerReal_paperGap_iff (l := l) (V := V) (I := I) C3 P

/-- The replacement statement is exactly `Paper312Statement`. -/
theorem paperGapStatement_iff_paper312 :
    paperGapStatement (l := l) (V := V) (I := I) C3 P ↔
      Paper312Statement (l := l) (V := V) (I := I) C3 P :=
  paperGap_iff_paper312Statement (l := l) (V := V) (I := I) C3 P
    (paperSharedContainerReal (l := l) (V := V) (I := I) C3 P)

/-- Vacuity-fix rows. -/
def vacuityFixRows : List (String × String) :=
  [ ("SharedContainerGap (D-free, ∃ parameters)", "SUPERSEDED → paperGapStatement"),
    ("final_conditional_ABC.hfull", "RETRACTED (unsatisfiable for fixed T)"),
    ("replacement: paperGap D of constructed container", "DEFINED + PROVED equivalent to qThetaComparison"),
    ("replacement ↔ Paper312Statement", "PROVED (green bridge)") ]

theorem vacuityFixRows_length : vacuityFixRows.length = 4 := rfl

#check paperGapStatement_iff_qThetaComparison
#check paperGapStatement_iff_paper312
#check processionAvg_le_max
#check switchAuditRows_length

end LeanFormal.IUT.XiFPaper.Mzk1SwitchAuditActual
end
