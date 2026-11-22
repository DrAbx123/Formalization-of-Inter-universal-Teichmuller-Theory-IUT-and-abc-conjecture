/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.MeasureTheory.Measure.MeasureSpace
import tmp.sheaf.gogopex.Iut.Stage1.CorollarySchema
import tmp.sheaf.gogopex.Iut.Stage1.PilotComparison

/-!
# A522 direction audit: the monotone log-volume route and the signed xi-f direction

Finding: `Mzk1MonotoneGogopexBridgeActual` uses POSITIVE magnitudes `qVol, hVol > 0`
and derives `-hVol >= -qVol` from `qVol <= hVol` — that is the reverse of real
arithmetic (`qVol <= hVol` gives `-hVol <= -qVol`, not `>=`).  With Gogopex's
`Corollary312Inequality theta q := -theta.value >= -q.value`, positive magnitudes give
the paper inequality `-|log(Theta)| >= -|log q|` iff `hVol = |log(Theta)| <= |log q| = qVol`,
so the monotone-containment route must use SIGNED log-volumes directly:

  signedLogVolume S := log(measure S)   (negative for the actual hull regions),
  qRegion ⊆ hull ⟹ signedLogVolume qRegion <= signedLogVolume hull,

and `signedLogVolume qRegion = -|log q|`, `signedLogVolume hull = -|log(Theta)|`, so the
SIGNED inequality `-|log q| <= -|log(Theta)|` (paper Cor 3.12) follows directly from the
containment with NO negation step and NO extra sign assumption.

This file proves the correct version (`signedLogVolume` monotone; `monotone_signed_direction`
as the subset-to-signed implication) and records the exact arithmetic obstruction of the
positive-magnitude version (`positive_magnitude_direction_false`).
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1MonotoneSignedDirectionActual

open LeanFormal.IUT

/-! ## 1. Signed log-volume monotone under inclusion (the correct setting) -/

/-- The SIGNED log-volume of a finite-measure region: `log(measure S)`.  For the actual
  hull regions this is the paper's negative reading (`-|log q|`, `-|log(Theta)|`). -/
def signedLogVolume {X : Type*} [MeasurableSpace X] (mu : MeasureTheory.Measure X)
    (S : Set X) : ℝ :=
  Real.log (mu S).toReal

/-- **Correct monotone direction**: a subregion has at most the signed log-volume of its
  container (measure monotonicity + `Real.log` monotonicity), for positive finite measure
  regions. -/
theorem signedLogVolume_mono {X : Type*} [MeasurableSpace X]
    (mu : MeasureTheory.Measure X) {S T : Set X} (hST : S ⊆ T)
    (hS : 0 < mu S) (hT : mu T ≠ ⊤) :
    signedLogVolume mu S ≤ signedLogVolume mu T := by
  unfold signedLogVolume
  have hle : mu S ≤ mu T := MeasureTheory.measure_mono hST
  have hSpos : (0 : ℝ) < (mu S).toReal := by
    rw [ENNReal.toReal_pos_iff]
    exact ⟨hS, ne_top_of_le_ne_top hT hle⟩
  have hTpos : (0 : ℝ) < (mu T).toReal := by
    rw [ENNReal.toReal_pos_iff]
    exact ⟨lt_of_lt_of_le hS hle, hT⟩
  exact Real.log_le_log hSpos (ENNReal.toReal_mono hT hle)

/-- **Self-check: subset ⟹ signed inequality, directly**.  For any real-valued
  `logVolume` that is monotone under inclusion, `S ⊆ T` gives `logVolume S <= logVolume T`;
  when `logVolume` is the signed reading this IS the paper inequality
  `-|log q| <= -|log(Theta)|`. -/
theorem monotone_signed_direction {X : Type*} (logVolume : Set X → ℝ)
    (mono : ∀ {S T : Set X}, S ⊆ T → logVolume S ≤ logVolume T)
    {S T : Set X} (hST : S ⊆ T) :
    logVolume S ≤ logVolume T :=
  mono hST

/-- The xi-f signed inequality from the containment, with the signed log-volume. -/
theorem xi_e_signed_direction {X : Type*} [MeasurableSpace X]
    (mu : MeasureTheory.Measure X) {qRegion hull : Set X} (h : qRegion ⊆ hull)
    (hq : 0 < mu qRegion) (hh : mu hull ≠ ⊤) :
    signedLogVolume mu qRegion ≤ signedLogVolume mu hull :=
  signedLogVolume_mono mu h hq hh

/-! ## 2. The positive-magnitude version: exact obstruction -/

/-- **Arithmetic obstruction**: if `qVol ≤ hVol` then the reversed claim
  `-hVol ≥ -qVol` is equivalent to `hVol ≤ qVol`, hence forces equality.  So the
  positive-magnitude route of `Mzk1MonotoneGogopexBridgeActual` cannot produce the
  declared signed comparison from containment alone. -/
theorem positive_magnitude_direction_obstruction {qVol hVol : ℝ} (h : qVol ≤ hVol)
    (hlt : qVol < hVol) : ¬ (-hVol ≥ -qVol) := by
  intro hge
  linarith

/-- The positive-magnitude formulation forces `hVol <= qVol`: with Gogopex
  `Corollary312Inequality theta q = (-theta.value >= -q.value)` and values
  `theta.value = hVol`, `q.value = qVol`, the statement is `hVol <= qVol`. -/
theorem gogopex_inequality_iff_magnitude {hVol qVol : ℝ} :
    Iut.Stage1.Corollary312Inequality
      ⟨Iut.Stage1.PilotSide.theta, hVol⟩
      ⟨Iut.Stage1.PilotSide.q, qVol⟩ ↔ hVol ≤ qVol := by
  unfold Iut.Stage1.Corollary312Inequality
  constructor <;> intro h <;> linarith

/-- The correct positive-magnitude direction for Cor 3.12: `|log(Theta)| <= |log q|`
  (equivalently `-|log(Theta)| >= -|log q|`).  It is the REVERSE of the containment
  monotonicity `qVol <= hVol`, so it must come from the q-pilot/Θ-pilot containment
  combined with the *signed* readings (Section 1), not from positive magnitudes. -/
theorem paper_magnitude_direction_of_signed {qVol hVol : ℝ}
    (h : -hVol ≥ -qVol) : hVol ≤ qVol := by
  linarith

end

end LeanFormal.IUT.XiFPaper.Mzk1MonotoneSignedDirectionActual