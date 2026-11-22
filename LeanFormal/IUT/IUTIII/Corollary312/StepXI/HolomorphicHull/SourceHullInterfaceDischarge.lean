import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceHullCompactnessReduction
import LeanFormal.IUT.Foundations.Volumes.HaarLogVolume

/-!
  # Discharge attempt: the finiteness field of `IQHullLogVolumeInterface`

  This module records the attempt to discharge the boundedness/finiteness content of
  `IQHullLogVolumeInterface` from the closest structures available in the tree, and the
  precise outcome.

  The four supplier structures examined:

  * `GeometricKernelValueLedger` (`IUTIII/Theorem311/SourceGeometricKernelLedger.lean`):
    the multiplicative action of the procession group on `FPrimeStrip.Mon` and the
    multiplicative degree; purely algebraic, with no set-level volume functional and no
    hull carrier.
  * the theta-packet ledger with `log_scale`/`log_volume` (`GeometricKernelPacketLedger`,
    same file): normalization of the packet scale against the period `q`; a finite real
    sum over the packet index, not a volume on a hull carrier.
  * `Foundations/Volumes/HaarLogVolume.lean`: addHaar closed-ball finiteness and the real
    scaling law in a finite-dimensional real normed space; a normalization analogue, but
    the tree contains no normed-space model of the value-monoid hull carrier.
  * `q_contracting` (`SourceRealizationLifting.lean`, `ConcreteTateLocalCarrier.lean`):
    `‖q‖ < 1`, a bound on the period parameter, not on the scaling classes of the hull.

  Outcome, family by family:

  * (F1) Positive: on any finite-dimensional real normed space, the additive Haar measure
    with a contracting scaling `x ↦ c • x`, `0 < c ≤ 1` (the `‖q‖ < 1` direction), and
    the closed unit ball as unit region realizes `IQHullLogVolumeInterface`
    (`haarContractionInterface`).  The interface's finiteness field is then a theorem
    (`haarContractionInterface_hull_logVolume_lt_top`).  So the analytic shape of the
    closest available Haar structure does imply finiteness, under the explicit named
    hypotheses: a normed carrier model exists, the scaling is a contraction, and the unit
    region is a compact closed ball.
  * (F2) Obstruction: on the value-monoid realization, under the pointwise degree
    faithfulness under which the log-volume formulas of `SourceImageHullVolume` hold, the
    paper-shaped input ("hull contained in a `λ`-multiple of a log-shell-bounded unit
    region") is unsatisfiable
    (`not_exists_scaledRegionImage_unitDegreeBounded_of_degreeFaithful`), and the hull
    volume is `⊤` (`sourceHullVolume_not_lt_top_of_degreeFaithful`).  Hence no
    instantiation of the interface whose `logVolume` is the value-level hull volume can
    satisfy its finiteness field in that regime, and none of the four algebraic
    structures above repairs this: none of them constrains `logVolume` on any hull
    carrier.
  * (F3) Transfer: for any realized interface, the finite hull log-volume is
    representable as `ENNReal.ofReal M` with `M = (logVolume hull).toReal`, preserving any
    normalized lower bound (`hull_logVolume_realRepresentation`) — the real-valued
    packaging that the step-XI consumer chain (`FiniteCertificateBridge`) consumes.

  The minimal extra hypothesis that is sufficient and closest to the paper is therefore
  the carrier-level datum named by `IQHullLogVolumeInterface` itself (finite normalized
  unit region, hull inside the normalized scaling region).  At the value level the same
  shape is `ValueHullCompactnessInput`, sufficient for finiteness
  (`sourceHullVolume_lt_top_of_compactnessInput`) but provably inconsistent with degree
  faithfulness (`not_nonempty_valueHullCompactnessInput_of_degreeFaithful`).  Nothing here
  is claimed about the actual `IQ(S±_{j+1}; n,◦D^vdash_{vQ})` carrier.

  Candidate status: (F1) is a consistency model, not a realization of the source
  carrier; (F2) and (F3) are proved.  The discharge of the source realization remains
  open by exactly the gap recorded in the audit obligation `iqHullInterfaceDischarge`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT

open MeasureTheory

universe u ua uv upi umon ui

noncomputable section

/-! ## 1. Real-valued packaging of the bounded hull log-volume (F3) -/

namespace IQHullLogVolumeInterface

variable {X : Type u} (W : IQHullLogVolumeInterface X)

/-- The finite hull log-volume of a realized interface is the `ENNReal.ofReal` of its
real part, and any normalized lower bound on the image union passes to that real part:
the transfer needed by the real-valued consumer chain. -/
theorem hull_logVolume_realRepresentation {lowerBound : ENNReal}
    (h : lowerBound ≤ W.logVolume W.imageSet) :
    ∃ M : ℝ, W.logVolume W.hull = ENNReal.ofReal M ∧
      lowerBound ≤ ENNReal.ofReal M := by
  refine ⟨(W.logVolume W.hull).toReal, ?_, ?_⟩
  · exact (ENNReal.ofReal_toReal (ne_top_of_lt W.hull_logVolume_lt_top)).symm
  · calc lowerBound ≤ W.logVolume W.hull := (W.lower_bound_and_finiteness h).1
      _ = ENNReal.ofReal (W.logVolume W.hull).toReal :=
          (ENNReal.ofReal_toReal (ne_top_of_lt W.hull_logVolume_lt_top)).symm

end IQHullLogVolumeInterface

/-! ## 2. The Haar-contraction model of the interface (F1)

The closest available analytic structure — the additive Haar measure of
`HaarLogVolume.lean` — realizes the interface exactly when a normed carrier model and a
contracting scaling are assumed.  This is a model statement; it does not claim that the
source carrier of Corollary 3.12 admits such a model. -/

/-- The Haar-contraction model of `IQHullLogVolumeInterface` on a finite-dimensional
real normed space: the unit region is the closed unit ball, the image union and hull are
the closed ball of radius `c`, and `scaleShift` is the contraction `x ↦ c • x` with
`0 < c ≤ 1`.  The hull sits inside the contraction of the unit ball, so monotonicity of
the Haar measure and finiteness of compact balls give the finiteness field. -/
def haarContractionInterface (E : Type u)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1) :
    IQHullLogVolumeInterface E where
  imageSet := Metric.closedBall (0 : E) c
  hull := Metric.closedBall (0 : E) c
  imageSet_subset_hull := subset_rfl
  logVolume := (Measure.addHaar : Measure E)
  logVolume_mono := fun hST => MeasureTheory.measure_mono hST
  unitRegion := Metric.closedBall (0 : E) 1
  scaleShift := fun x => c • x
  hull_subset_scaleShift := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    refine ⟨c⁻¹ • x, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hc0)]
      calc c⁻¹ * ‖x‖ ≤ c⁻¹ * c :=
            mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hc0.le)
        _ = 1 := inv_mul_cancel₀ hc0.ne'
    · change c • (c⁻¹ • x) = x
      rw [smul_smul, mul_inv_cancel₀ hc0.ne']
      exact one_smul ℝ x
  unitRegion_logVolume_lt_top :=
    (isCompact_closedBall (0 : E) 1).measure_lt_top
  scaleShift_unitRegion_logVolume_le := by
    refine MeasureTheory.measure_mono ?_
    intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hy
    change c • y ∈ Metric.closedBall (0 : E) 1
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos hc0]
    calc c * ‖y‖ ≤ c * 1 := mul_le_mul_of_nonneg_left hy hc0.le
      _ = c := mul_one c
      _ ≤ 1 := hc1

/-- Finiteness of the hull log-volume in the Haar-contraction model: the interface field
obtained from a normed carrier, a contracting scaling and a compact ball unit region. -/
theorem haarContractionInterface_hull_logVolume_lt_top (E : Type u)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1) :
    (haarContractionInterface E c hc0 hc1).logVolume
        (haarContractionInterface E c hc0 hc1).hull < ⊤ :=
  (haarContractionInterface E c hc0 hc1).hull_logVolume_lt_top

end

/-! ## 3. Value-level obstruction (F2) and the named value-level input -/

namespace Theorem311Source
namespace OriginalInput

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- Under pointwise degree faithfulness the value-realized hull volume is not finite:
the finiteness obligation of the interface fails for `logVolume := sourceHullVolume` in
exactly the regime where the value-level log-volume formulas hold. -/
theorem sourceHullVolume_not_lt_top_of_degreeFaithful (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hdeg : ∀ b : ℝ,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    ¬ I.sourceHullVolume v R n < ⊤ := by
  rw [I.sourceHullVolume_eq_top_of_degreeFaithful v R n hdeg]
  exact not_lt_of_ge le_rfl

/-- Under pointwise degree faithfulness there is no paper-shaped compactness input for
the value-level hull: no scaling `λ`, unit region `O` and bound `C` with the hull inside
the `λ`-multiple of `O` and all of `O` of log-degree at most `C`.  The scaled region is
degree-bounded by additivity of the log-degree, contradicting the unboundedness of the
hull log-degree. -/
theorem not_exists_scaledRegionImage_unitDegreeBounded_of_degreeFaithful (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hdeg : ∀ b : ℝ,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    ¬ ∃ (scaling : I.ThetaPilotPoint v) (O : Set (I.ThetaPilotPoint v)) (C : ℝ),
        (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) ⊆
          scaledRegionImage scaling O ∧
        (∀ y ∈ O, I.sourceLocalLogDegree v y ≤ C) := by
  rintro ⟨scaling, O, C, hHull, hO⟩
  obtain ⟨x, hx, hgt⟩ :=
    I.sourceHolomorphicHull_logDegree_unbounded v R n hdeg
      (C + I.sourceLocalLogDegree v scaling)
  obtain ⟨y, hyO, rfl⟩ := (mem_scaledRegionImage_iff).mp (hHull hx)
  have hmul := I.sourceLocalLogDegree_mul v scaling y
  have hy := hO y hyO
  linarith

/-- The named value-level compactness input: a scaling `λ`, a unit region `O` and a
log-degree bound `C` with the hull inside the `λ`-multiple of `O` and `O` of log-degree
at most `C`.  This is the exact paper shape (`hull ⊆ λ·O`, `O` log-shell bounded) at the
value-monoid level, recorded as named data; it is not claimed to follow from
`OriginalInput`. -/
structure ValueHullCompactnessInput (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) where
  /-- The scaling `λ` of the `λ·O` region. -/
  scaling : I.ThetaPilotPoint v
  /-- The unit region `O`. -/
  unitRegion : Set (I.ThetaPilotPoint v)
  /-- The log-degree bound `C` on the unit region. -/
  degreeBound : ℝ
  /-- The hull is contained in the `λ`-multiple of the unit region. -/
  hull_subset_scaledRegionImage :
    (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) ⊆
      scaledRegionImage scaling unitRegion
  /-- Every point of the unit region has log-degree at most the bound. -/
  unitRegion_logDegree_le :
    ∀ y ∈ unitRegion, I.sourceLocalLogDegree v y ≤ degreeBound

/-- The named value-level compactness input is sufficient for finiteness of the
value-realized hull volume (the reduction of `SourceImageHullVolume`). -/
theorem sourceHullVolume_lt_top_of_compactnessInput (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (H : I.ValueHullCompactnessInput v R n) :
    I.sourceHullVolume v R n < ⊤ :=
  I.sourceHullVolume_lt_top_of_scaledRegionImage v R n
    H.hull_subset_scaledRegionImage H.unitRegion_logDegree_le

/-- Under pointwise degree faithfulness the named value-level compactness input is
inconsistent: no data of this paper shape can exist for the value-realized hull. -/
theorem not_nonempty_valueHullCompactnessInput_of_degreeFaithful (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hdeg : ∀ b : ℝ,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    ¬ Nonempty (I.ValueHullCompactnessInput v R n) := by
  rintro ⟨H⟩
  exact I.not_exists_scaledRegionImage_unitDegreeBounded_of_degreeFaithful v R n hdeg
    ⟨H.scaling, H.unitRegion, H.degreeBound,
      H.hull_subset_scaledRegionImage, H.unitRegion_logDegree_le⟩

end OriginalInput
end Theorem311Source

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for the discharge attempt of the Corollary 3.12 hull-interface
finiteness field: positive Haar-contraction model, value-level obstruction under degree
faithfulness, and the real-valued transfer. -/
def iqHullInterfaceDischarge : Obligation :=
  { id := "IUT-III.corollary-3.12-iq-hull-interface-discharge"
    source :=
      "IUT III, Corollary 3.12 proof (compactness of the 1,circ U_{j,vQ} and the " ++
        "definition of the log-volume); Remark 3.9.5, (i), (ii)"
    status := VerificationStatus.interface
    note :=
      "Discharge attempt for the finiteness field of IQHullLogVolumeInterface. " ++
        "Proved: (F1) on any finite-dimensional real normed space the additive Haar " ++
        "measure, a contracting scaling x |-> c • x (0 < c <= 1, the q_contracting " ++
        "direction) and the closed unit ball realize the interface " ++
        "(haarContractionInterface), hence the finiteness field holds under those " ++
        "explicit carrier hypotheses; (F2) on the value-monoid realization, under " ++
        "pointwise degree faithfulness the paper-shaped input (hull inside a " ++
        "lambda-multiple of a log-degree-bounded unit region) is unsatisfiable " ++
        "(not_exists_scaledRegionImage_unitDegreeBounded_of_degreeFaithful) and the " ++
        "hull volume is top (sourceHullVolume_not_lt_top_of_degreeFaithful), so no " ++
        "value-level logVolume of the hull can satisfy the field there; (F3) any " ++
        "realized interface transfers to a real-valued representation of the finite " ++
        "hull log-volume preserving normalized lower bounds " ++
        "(hull_logVolume_realRepresentation). NOT proved: that the actual " ++
        "IQ(S±_{j+1}; n,circ D^vdash_{vQ}) carrier realizes the interface. Of the " ++
        "examined supplier structures, GeometricKernelValueLedger (algebraic " ++
        "action/degree), the packet log_scale/log_volume (finite real normalization), " ++
        "HaarLogVolume (normed-space scaling law) and q_contracting (period bound) " ++
        "none supplies the carrier-level unit-region/Haar datum; the minimal " ++
        "sufficient addition is exactly that datum."
    dependsOn :=
      [ "IUT-III.corollary-3.12-iq-hull-log-volume-interface",
        "IUT-III.corollary-3.12-source-image-hull-volume" ] }

end LeanFormal.IUT.Audit
