import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealEdgeNormalizationDichotomy

/-!
# R9 finite-phase gate: the `toReal` two-phase anti-fake-pass package (report T3)

Task `hunit-epsilon-transfer-20261016`.  The hull volume `sourceHullVolume` is
an `ENNReal`; `ENNReal.toReal top = 0`.  Hence any comparison channeled
through `.toReal` is blind to the infinite phase: `(hull).toReal = 0` makes the
comparison `(hull).toReal <= (image).toReal` vacuously true even when the
ENNReal comparison `hull <= image` fails.  This file makes the two phases
exact:

* positive-degree hull points force the infinite phase
  (`sourceHullVolume_eq_top_of_exists_pos_logDegree`), and conversely
  (`sourceHullVolume_eq_top_iff_exists_pos_logDegree`);
* R9 holds exactly in the finite phase (`sourceHullVolume_le_imageVolume_iff_lt_top`);
* finite hull volume is equivalent to all hull log-degrees being nonpositive
  (`sourceHullVolume_lt_top_iff_forall_logDegree_nonpos`), so
  `R9 iff no positive-degree hull point` (`..._iff_not_exists_pos_logDegree`);
* the `toReal` channel is dead at the infinite phase
  (`sourceHullVolume_toReal_eq_zero_of_eq_top`,
  `sourceHullVolume_toReal_le_imageVolume_toReal_of_eq_top`) and faithful only
  under the finite-phase hypothesis
  (`sourceHullVolume_toReal_le_imageVolume_toReal_iff_of_lt_top`);
* the generic fake-pass calibration
  (`toReal_top_collapse_calibration`,
  `toReal_channel_not_faithful_calibration`).

Checklist of the existing `.toReal` transmission points (all already guarded by
a finiteness hypothesis; the gate explains why the guard is not optional):
`CardHullRealEdgeNormalizationDichotomy.lean:333,350-356` (guard
`sourceImageVolume_lt_top`);
`CardHullRealSignedLogVolume.lean:164-168,184-190` (guard `hfin`);
`CardHullRealGeometryReduction.lean:354-373` (guard `hfinImg`).

Boundary: the `degreeFaithful` top-premise of the O1 note
(`sourceHullVolume_eq_top_of_degreeFaithful`) is NOT used as evidence here
(its premise space is empty); the phase dichotomy proved here is
unconditional.  Card-HULLREAL and the R9 body remain open.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT
universe u v ua uv upi umon ui


/-- **The `toReal`-top collapse.** -/
theorem toReal_top_collapse_calibration :
    (⊤ : ENNReal).toReal ≤ (0 : ENNReal).toReal ∧ ¬ ((⊤ : ENNReal) ≤ (0 : ENNReal)) :=
  ⟨by simp, not_le_of_gt ENNReal.zero_lt_top⟩

/-- **The `toReal` channel is not faithful in general**: there are volumes whose
`toReal` comparison holds while the `ENNReal` comparison fails. -/
theorem toReal_channel_not_faithful_calibration :
    ∃ (a b : ENNReal), a.toReal ≤ b.toReal ∧ ¬ a ≤ b :=
  ⟨⊤, 0, by simp, not_le_of_gt ENNReal.zero_lt_top⟩

namespace Theorem311Source
namespace OriginalInput

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- **Positive degree forces the infinite phase.**  If a hull point has strictly
positive log-degree then the powers of that point stay in the hull with
unbounded log-volumes, so the hull volume is `top`.  Unconditional (no
degree-faithfulness premise). -/
theorem sourceHullVolume_eq_top_of_exists_pos_logDegree (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (h : ∃ x ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)),
      0 < I.sourceLocalLogDegree v x) :
    I.sourceHullVolume v R n = ⊤ := by
  obtain ⟨x, hx, hpos⟩ := h
  by_contra hne
  have hsup : ∀ k : ℕ,
      ENNReal.ofReal ((k : Real) * I.sourceLocalLogDegree v x) ≤
        I.sourceHullVolume v R n := by
    intro k
    have hpow : x ^ k ∈
        (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) :=
      Submonoid.pow_mem (I.sourceHolomorphicHull v R n) hx k
    calc ENNReal.ofReal ((k : Real) * I.sourceLocalLogDegree v x)
        = I.sourcePointVolume v (x ^ k) := by
          unfold sourcePointVolume
          rw [I.sourceLocalLogDegree_pow]
      _ ≤ I.sourceHullVolume v R n := by
          unfold sourceHullVolume sourceSetVolume
          exact le_iSup_of_le (x ^ k) (le_iSup_of_le hpow le_rfl)
  have hle : ∀ k : ℕ,
      (k : Real) * I.sourceLocalLogDegree v x ≤ (I.sourceHullVolume v R n).toReal :=
    fun k => (ENNReal.ofReal_le_iff_le_toReal hne).mp (hsup k)
  obtain ⟨k, hk⟩ := exists_nat_gt
    ((I.sourceHullVolume v R n).toReal / I.sourceLocalLogDegree v x)
  have hk' : (I.sourceHullVolume v R n).toReal <
      (k : Real) * I.sourceLocalLogDegree v x := by
    have h' := mul_lt_mul_of_pos_right hk hpos
    rwa [div_mul_cancel₀ _ (ne_of_gt hpos)] at h'
  exact not_lt_of_ge (hle k) hk'

/-- **Phase dichotomy at the hull volume.**  The hull volume is infinite exactly
when a positive-degree point inhabits the hull. -/
theorem sourceHullVolume_eq_top_iff_exists_pos_logDegree (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    I.sourceHullVolume v R n = ⊤ ↔
      ∃ x ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)),
        0 < I.sourceLocalLogDegree v x := by
  constructor
  · intro htop
    by_contra hnex
    push Not at hnex
    have h0 := sourceHullVolume_eq_zero_of_hull_logDegree_nonpos I v R n hnex
    exact ENNReal.zero_ne_top (h0.symm.trans htop)
  · exact sourceHullVolume_eq_top_of_exists_pos_logDegree I v R n

/-- **Finite-phase gate: R9 holds exactly in the finite phase.**  Combining the
finite edge volume with the phase dichotomy. -/
theorem sourceHullVolume_le_imageVolume_iff_lt_top (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    I.sourceHullVolume v R n ≤ I.sourceImageVolume v R n ↔
      I.sourceHullVolume v R n < ⊤ := by
  constructor
  · intro h
    exact lt_of_le_of_lt h (sourceImageVolume_lt_top I v R n)
  · intro hlt
    rw [sourceHullVolume_le_imageVolume_iff_hull_logDegree_nonpos I v R n]
    by_contra h'
    push Not at h'
    obtain ⟨z, hz, hpos⟩ := h'
    exact (ne_of_lt hlt)
      (sourceHullVolume_eq_top_of_exists_pos_logDegree I v R n ⟨z, hz, hpos⟩)

/-- Finite hull volume is equivalent to all hull log-degrees being
nonpositive. -/
theorem sourceHullVolume_lt_top_iff_forall_logDegree_nonpos (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    I.sourceHullVolume v R n < ⊤ ↔
      ∀ z ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)),
        I.sourceLocalLogDegree v z ≤ 0 := by
  constructor
  · intro hlt
    by_contra h'
    push Not at h'
    obtain ⟨z, hz, hpos⟩ := h'
    exact (ne_of_lt hlt)
      (sourceHullVolume_eq_top_of_exists_pos_logDegree I v R n ⟨z, hz, hpos⟩)
  · intro h
    rw [sourceHullVolume_eq_zero_of_hull_logDegree_nonpos I v R n h]
    exact ENNReal.zero_lt_top

/-- **Anti-fake-pass R9 form.**  R9 holds exactly when no positive-degree point
inhabits the hull. -/
theorem sourceHullVolume_le_imageVolume_iff_not_exists_pos_logDegree (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    I.sourceHullVolume v R n ≤ I.sourceImageVolume v R n ↔
      ¬ ∃ z ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)),
        0 < I.sourceLocalLogDegree v z := by
  rw [sourceHullVolume_le_imageVolume_iff_lt_top I v R n,
    sourceHullVolume_lt_top_iff_forall_logDegree_nonpos I v R n]
  constructor
  · intro h h'ex
    obtain ⟨z, hz, hpos⟩ := h'ex
    exact (not_lt_of_ge (h z hz)) hpos
  · intro h z hz
    by_contra hz'
    exact h ⟨z, hz, not_le.mp hz'⟩

/-- The `toReal` value is zero in the infinite phase. -/
theorem sourceHullVolume_toReal_eq_zero_of_eq_top (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (h : I.sourceHullVolume v R n = ⊤) :
    (I.sourceHullVolume v R n).toReal = 0 := by
  rw [h, ENNReal.toReal_top]

/-- **Blank comparison at the infinite phase.**  If the hull volume is `top`,
the `toReal` comparison against the (always finite) edge volume holds
vacuously: the `toReal` channel cannot see that R9 itself fails. -/
theorem sourceHullVolume_toReal_le_imageVolume_toReal_of_eq_top (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (h : I.sourceHullVolume v R n = ⊤) :
    (I.sourceHullVolume v R n).toReal ≤ (I.sourceImageVolume v R n).toReal := by
  rw [h, ENNReal.toReal_top]
  exact ENNReal.toReal_nonneg

/-- **Faithful channel under the finite phase.**  In the finite phase the
`toReal` comparison is equivalent to the `ENNReal` comparison. -/
theorem sourceHullVolume_toReal_le_imageVolume_toReal_iff_of_lt_top (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hlt : I.sourceHullVolume v R n < ⊤) :
    (I.sourceHullVolume v R n).toReal ≤ (I.sourceImageVolume v R n).toReal ↔
      I.sourceHullVolume v R n ≤ I.sourceImageVolume v R n :=
  ENNReal.toReal_le_toReal (ne_of_lt hlt)
    (ne_of_lt (sourceImageVolume_lt_top I v R n))

end OriginalInput
end Theorem311Source

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for the T3 finite-phase / `.toReal` gate (report section 22). -/
def cardHullRealFinitePhaseGate : Obligation :=
  { id := "IUT-III.corollary-3.12-card-hullreal-finite-phase-gate"
    source :=
      "IUT III, Corollary 3.12, Step (xi): finiteness of -|log(Theta)| " ++
        "(III:10354-10360) and the normalization -|log(Theta)| < 0 " ++
        "(III:10843-10863, 10895-10899); Mathlib ENNReal.toReal top = 0"
    status := VerificationStatus.interface
    note :=
      "T3 anti-fake-pass gate. Proved: positive-degree hull points force " ++
        "hullVolume = top (unconditional); hullVolume = top iff a " ++
        "positive-degree point inhabits the hull; R9 iff the hull volume is " ++
        "finite; finite hull volume iff all hull log-degrees are nonpositive; " ++
        "R9 iff no positive-degree hull point. The toReal channel collapses " ++
        "top to 0, so toReal comparisons are vacuous in the infinite phase and " ++
        "faithful iff the finite phase is exhibited. Checklist of existing " ++
        "toReal transmission points (all already guarded by finiteness): " ++
        "Dichotomy:333,350-356; SignedLogVolume:164-168,184-190; " ++
        "GeometryReduction:354-373. The degreeFaithful top-premise of the O1 " ++
        "note is NOT used (empty premise space)."
    dependsOn :=
      [ "IUT-III.corollary-3.12-card-hullreal-edge-normalization-dichotomy",
        "IUT-III.corollary-3.12-card-hullreal-edge-normalization-reduction" ] }

end LeanFormal.IUT.Audit
