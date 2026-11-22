import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceHullInterfaceDischarge
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.FiniteCertificateBridge
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.ThetaPacketBridge
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.SourceSharedBoundary

/-!
  # Wiring the hull log-volume interface into the Step-XI finite certificate

  This module proves the formal composition from a realization of
  `IQHullLogVolumeInterface` (or the Haar-contraction instance
  `haarContractionInterface`) for a hull carrier to the data shapes consumed by
  `FiniteCertificateBridge` (`StepXIFiniteCertificate`, `FiniteStepXILinkEvidence`,
  `Cor312Conclusion`), and records the exact remaining hypotheses as named lemmas.

  Family 1 (interface realization -> certificate assembly, `iqHull...`):
  * `iqHullRealVolume` is the real part of the hull log-volume of a realization,
    with nonnegativity and the exact `ENNReal.ofReal` reconstruction;
  * `iqHullFiniteHull` is the consumer's `FiniteHull` over any finite label type
    with a point map into the image union (per-point volumes are the singleton
    log-volumes; `contains` is monotonicity of the interface log-volume);
  * `iqHullFiniteHull_average_le` is the `WeightedValues` average bound consumed
    by `FiniteHull.average_le`;
  * `iqHullCertificate` is a full `StepXIFiniteCertificate` given the interface
    datum plus the explicit named hypotheses: a real `q` with
    `ofReal q <= logVolume imageSet`, a real `theta` with
    `logVolume hull <= ofReal theta`, `0 <= theta`, and `q < 0`;
  * `iqHullLinkEvidence` / `iqHullCor312Conclusion` complete the composition to
    `Cor312Conclusion` through the existing `FiniteCertificateBridge` assembly
    (with `targetSigned := iqHullRealVolume`), leaving only the unchanged
    IPL/SHE/APT evidence fields and the named hypotheses above.

  Family 2 (value-level source wiring, `source...`):
  * `sourceRealHullVolume` and its finiteness transfer
    (`sourceHullVolume_eq_ofReal`, lower/upper transfer lemmas,
    `sourceRealHullVolume_ge_normalized` for the procession-normalized bound);
  * `sourceThetaPilotFiniteHull`: the consumer's `FiniteHull` over the signed
    labels at the fixed procession (the packet label type of `ThetaPacketBridge`),
    available exactly under the finiteness input;
  * `thetaValueAt_eq_oneColumnScale` and
    `thetaValueAt_eq_toPositivePacket_scale`: the theta special values entering
    the normalized bound are the one-column ledger scales of
    `SourceSharedBoundary` / `ThetaPacketBridge`.

  Family 3 (interface-correction lemmas): the consumer's real upper-bound field
  (`hull_le_theta` / `target_le_theta`) is *exactly equivalent* to an interface
  level `ENNReal` upper bound (`iqHullRealVolume_le_theta_iff`); the interface's
  proved finiteness does not supply it.  At the value level that field is
  unsatisfiable under pointwise degree faithfulness
  (`sourceThetaBound_unsat_of_degreeFaithful`), and the negativity of the
  normalized lower bound is exactly the packet contraction condition
  `thetaValueAt < 1` (`sourceThetaValue_neg_iff`).

  Candidate status: the composition is proved; the realization `W`, the two
  `ENNReal` bounds, `0 <= theta`, `q < 0`, and the IPL/SHE/APT evidence remain
  supplied hypotheses, never derived here, and nothing is claimed about the
  actual `IQ(S±_{j+1}; n,◦D^vdash_{vQ})` carrier.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT

universe u v ua uv upi umon ui

noncomputable section

/-! ## 1. `ENNReal`-to-`Real` transfer lemmas -/

/-- An `ENNReal.ofReal q` lower bound on a finite extended value is a real lower
bound on its real part. -/
theorem ofReal_le_toReal_of_ne_top {q : ℝ} {a : ENNReal} (hne : a ≠ ⊤)
    (h : ENNReal.ofReal q ≤ a) : q ≤ a.toReal := by
  rw [← ENNReal.ofReal_toReal hne] at h
  exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp h

/-- An `ENNReal.ofReal theta` upper bound with `0 ≤ theta` is a real upper bound on
the real part of an extended value. -/
theorem toReal_le_of_le_ofReal {a : ENNReal} {θ : ℝ} (hθ0 : 0 ≤ θ)
    (h : a ≤ ENNReal.ofReal θ) : a.toReal ≤ θ := by
  have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rw [ENNReal.toReal_ofReal hθ0] at h1
  exact h1

/-! ## 2. Interface realization -> finite certificate (family 1) -/

/-- The real part of the hull log-volume of a realized interface: the real-valued
hull volume consumed by `FiniteHull.hullVolume`. -/
def iqHullRealVolume {X : Type u} (W : IQHullLogVolumeInterface X) : ℝ :=
  (W.logVolume W.hull).toReal

theorem iqHullRealVolume_nonneg {X : Type u} (W : IQHullLogVolumeInterface X) :
    0 ≤ iqHullRealVolume W :=
  ENNReal.toReal_nonneg

/-- The finite hull log-volume of a realization is exactly the `ENNReal.ofReal` of
its real part. -/
theorem iqHull_logVolume_hull_eq_ofReal {X : Type u} (W : IQHullLogVolumeInterface X) :
    W.logVolume W.hull = ENNReal.ofReal (iqHullRealVolume W) :=
  (ENNReal.ofReal_toReal (ne_top_of_lt W.hull_logVolume_lt_top)).symm

/-- **Interface-correction lemma (family 3).**  The consumer's real upper-bound
field is exactly equivalent to an interface-level `ENNReal` upper bound: the
proved finiteness (`hull_logVolume_lt_top`) does not produce it. -/
theorem iqHullRealVolume_le_theta_iff {X : Type u} (W : IQHullLogVolumeInterface X)
    {θ : ℝ} (hθ0 : 0 ≤ θ) :
    iqHullRealVolume W ≤ θ ↔ W.logVolume W.hull ≤ ENNReal.ofReal θ := by
  constructor
  · intro h
    rw [iqHull_logVolume_hull_eq_ofReal W]
    exact ENNReal.ofReal_le_ofReal h
  · intro h
    exact toReal_le_of_le_ofReal hθ0 h

/-- The consumer's `FiniteHull` over any finite label type with a point map into the
image union of a realization. -/
def iqHullFiniteHull {X : Type u} (W : IQHullLogVolumeInterface X)
    {label : Type v} [Fintype label] (pt : label → X)
    (hpt : ∀ i, pt i ∈ W.imageSet) : FiniteHull label where
  volume := fun i => (W.logVolume {pt i}).toReal
  hullVolume := iqHullRealVolume W
  contains := fun i =>
    ENNReal.toReal_mono (ne_top_of_lt W.hull_logVolume_lt_top)
      (W.logVolume_mono (by
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact W.imageSet_subset_hull (hpt i)))

@[simp] theorem iqHullFiniteHull_volume {X : Type u} (W : IQHullLogVolumeInterface X)
    {label : Type v} [Fintype label] (pt : label → X)
    (hpt : ∀ i, pt i ∈ W.imageSet) (i : label) :
    (iqHullFiniteHull W pt hpt).volume i = (W.logVolume {pt i}).toReal := rfl

@[simp] theorem iqHullFiniteHull_hullVolume {X : Type u}
    (W : IQHullLogVolumeInterface X)
    {label : Type v} [Fintype label] (pt : label → X)
    (hpt : ∀ i, pt i ∈ W.imageSet) :
    (iqHullFiniteHull W pt hpt).hullVolume = iqHullRealVolume W := rfl

/-- The `WeightedValues` average bound consumed by `FiniteHull.average_le`, assembled
from an interface realization. -/
theorem iqHullFiniteHull_average_le {X : Type u} (W : IQHullLogVolumeInterface X)
    {label : Type v} [Fintype label] (pt : label → X)
    (hpt : ∀ i, pt i ∈ W.imageSet) (data : WeightedValues label)
    (hvalue : ∀ i, data.value i = (iqHullFiniteHull W pt hpt).volume i)
    (hw : ∀ i, 0 ≤ data.weight i) :
    data.average ≤ iqHullRealVolume W :=
  FiniteHull.average_le (iqHullFiniteHull W pt hpt) data hvalue hw

/-- **Family 1 assembly.**  A full `StepXIFiniteCertificate` from an interface
realization, a finite labeling, `WeightedValues` bookkeeping, and the explicit named
hypotheses on the real numbers `q` and `theta` and on the interface-level bounds. -/
def iqHullCertificate {X : Type u} (W : IQHullLogVolumeInterface X)
    {label : Type v} [Fintype label] (pt : label → X)
    (hpt : ∀ i, pt i ∈ W.imageSet) (data : WeightedValues label)
    (hvalue : ∀ i, data.value i = (iqHullFiniteHull W pt hpt).volume i)
    (hw : ∀ i, 0 ≤ data.weight i)
    (q θ : ℝ) (hq : ENNReal.ofReal q ≤ W.logVolume W.imageSet)
    (hθ : W.logVolume W.hull ≤ ENNReal.ofReal θ) (hθ0 : 0 ≤ θ) (hqneg : q < 0) :
    StepXIFiniteCertificate label where
  hull := iqHullFiniteHull W pt hpt
  weighted := data
  weighted_matches_hull := hvalue
  weights_nonnegative := hw
  qSigned := q
  thetaSigned := θ
  q_le_hull := by
    have hq' : ENNReal.ofReal q ≤ W.logVolume W.hull :=
      le_trans hq (W.logVolume_mono W.imageSet_subset_hull)
    exact ofReal_le_toReal_of_ne_top (ne_top_of_lt W.hull_logVolume_lt_top) hq'
  hull_le_theta := toReal_le_of_le_ofReal hθ0 hθ
  q_negative := hqneg

/-- The link evidence of `FiniteCertificateBridge` for the interface certificate, with
`targetSigned := iqHullRealVolume`; the IPL/SHE/APT propositions and their evidence
are supplied externally, exactly as in the existing bridge. -/
def iqHullLinkEvidence {X : Type u} (W : IQHullLogVolumeInterface X)
    {label : Type v} [Fintype label] (pt : label → X)
    (hpt : ∀ i, pt i ∈ W.imageSet) (data : WeightedValues label)
    (hvalue : ∀ i, data.value i = (iqHullFiniteHull W pt hpt).volume i)
    (hw : ∀ i, 0 ≤ data.weight i)
    (q θ : ℝ) (hq : ENNReal.ofReal q ≤ W.logVolume W.imageSet)
    (hθ : W.logVolume W.hull ≤ ENNReal.ofReal θ) (hθ0 : 0 ≤ θ) (hqneg : q < 0)
    (ipl she apt : Prop) (hipl : ipl) (hshe : she) (hapt : apt) :
    FiniteStepXILinkEvidence
      (iqHullCertificate W pt hpt data hvalue hw q θ hq hθ hθ0 hqneg) where
  targetSigned := iqHullRealVolume W
  ipl := ipl
  she := she
  apt := apt
  ipl_evidence := hipl
  she_evidence := hshe
  apt_evidence := hapt
  q_le_target :=
    (iqHullCertificate W pt hpt data hvalue hw q θ hq hθ hθ0 hqneg).q_le_hull
  target_le_theta :=
    (iqHullCertificate W pt hpt data hvalue hw q θ hq hθ hθ0 hqneg).hull_le_theta

/-- **Family 1 headline composition.**  From an interface realization and the named
hypotheses, the existing `FiniteCertificateBridge` assembly yields the Corollary 3.12
contract conclusion. -/
theorem iqHullCor312Conclusion {X : Type u} (W : IQHullLogVolumeInterface X)
    {label : Type v} [Fintype label] (pt : label → X)
    (hpt : ∀ i, pt i ∈ W.imageSet) (data : WeightedValues label)
    (hvalue : ∀ i, data.value i = (iqHullFiniteHull W pt hpt).volume i)
    (hw : ∀ i, 0 ≤ data.weight i)
    (q θ : ℝ) (hq : ENNReal.ofReal q ≤ W.logVolume W.imageSet)
    (hθ : W.logVolume W.hull ≤ ENNReal.ofReal θ) (hθ0 : 0 ≤ θ) (hqneg : q < 0)
    (ipl she apt : Prop) (hipl : ipl) (hshe : she) (hapt : apt) :
    Cor312Conclusion
      ((iqHullCertificate W pt hpt data hvalue hw q θ hq hθ hθ0 hqneg).toContract
        (iqHullLinkEvidence W pt hpt data hvalue hw q θ hq hθ hθ0 hqneg
          ipl she apt hipl hshe hapt)) :=
  cor312_of_finite_certificate _ _

/-- Non-vacuity of `iqHullFiniteHull` from the Haar-contraction instance: a
`FiniteHull` realized by the additive Haar measure on a finite-dimensional real
normed space. -/
def haarContractionFiniteHull (E : Type u)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1) (label : Type v) [Fintype label] :
    FiniteHull label :=
  iqHullFiniteHull (haarContractionInterface E c hc0 hc1) (fun _ => (0 : E))
    (fun _ => by
      change (0 : E) ∈ Metric.closedBall (0 : E) c
      rw [Metric.mem_closedBall, dist_self]
      exact hc0.le)

/-! ## 3. Value-level source wiring (family 2) and corrections (family 3) -/

namespace Theorem311Source
namespace OriginalInput

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- The pilot carrier `ThetaPilotCarrier l` is a `Fin` type and therefore finite; the
plain `def` alias hides this from instance search, so it is recorded here. -/
instance thetaPilotCarrierFintype (l : PrimeGeFive) :
    Fintype (ThetaPilotCarrier l) :=
  inferInstanceAs (Fintype (Fin (lStar l.value + 1)))

/-- The real part of the value-realized hull log-volume. -/
def sourceRealHullVolume (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) : ℝ :=
  (I.sourceHullVolume v R n).toReal

theorem sourceRealHullVolume_nonneg (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) : 0 ≤ I.sourceRealHullVolume v R n :=
  ENNReal.toReal_nonneg

/-- Under finiteness, the value-realized hull log-volume is the `ENNReal.ofReal` of its
real part: the transfer into the real-valued consumer shape. -/
theorem sourceHullVolume_eq_ofReal (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) (hfin : I.sourceHullVolume v R n < ⊤) :
    I.sourceHullVolume v R n = ENNReal.ofReal (I.sourceRealHullVolume v R n) :=
  (ENNReal.ofReal_toReal (ne_top_of_lt hfin)).symm

/-- An `ENNReal.ofReal q` lower bound on the value-realized hull log-volume transfers
to a real lower bound, under finiteness. -/
theorem sourceRealHullVolume_ge_of_ofReal_le (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) {q : ℝ} (hfin : I.sourceHullVolume v R n < ⊤)
    (hq : ENNReal.ofReal q ≤ I.sourceHullVolume v R n) :
    q ≤ I.sourceRealHullVolume v R n :=
  ofReal_le_toReal_of_ne_top (ne_top_of_lt hfin) hq

/-- An `ENNReal.ofReal theta` upper bound with `0 ≤ theta` transfers to a real upper
bound on the value-realized hull log-volume. -/
theorem sourceRealHullVolume_le_theta (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : I.sourceHullVolume v R n ≤ ENNReal.ofReal θ) :
    I.sourceRealHullVolume v R n ≤ θ :=
  toReal_le_of_le_ofReal hθ0 hθ

/-- The procession-normalized lower bound of `sourceHullVolume_ge_normalized`,
transferred to the real part under finiteness. -/
theorem sourceRealHullVolume_ge_normalized (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l)
    (hdeg : ∀ b : ℝ,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b)
    (hfin : I.sourceHullVolume v R n < ⊤) (j₀ : SignedLabel l.value) :
    (Fintype.card (SourceVolumeIndex l) : ℝ) *
        Real.log (I.thetaValueAt (n.val : Int) 0 j₀) ≤
      I.sourceRealHullVolume v R n := by
  have h := I.sourceHullVolume_ge_normalized v R n hdeg j₀
  have h' : ENNReal.ofReal ((Fintype.card (SourceVolumeIndex l) : ℝ) *
        Real.log (I.thetaValueAt (n.val : Int) 0 j₀)) ≤
      ENNReal.ofReal (I.sourceRealHullVolume v R n) := by
    rw [show ENNReal.ofReal (I.sourceRealHullVolume v R n) =
        I.sourceHullVolume v R n from
      ENNReal.ofReal_toReal (ne_top_of_lt hfin)]
    exact h
  exact (ENNReal.ofReal_le_ofReal_iff
    (I.sourceRealHullVolume_nonneg v R n)).mp h'

/-- **Interface-correction lemma (family 3).**  At the value level, the consumer's real
upper-bound field is unsatisfiable under pointwise degree faithfulness: there is no real
`theta` bounding the value-realized hull log-volume from above. -/
theorem sourceThetaBound_unsat_of_degreeFaithful (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hdeg : ∀ b : ℝ,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    ¬ ∃ θ : ℝ, I.sourceHullVolume v R n ≤ ENNReal.ofReal θ := by
  rintro ⟨θ, hθ⟩
  rw [I.sourceHullVolume_eq_top_of_degreeFaithful v R n hdeg] at hθ
  exact not_le_of_gt ENNReal.ofReal_lt_top hθ

/-- The consumer's `FiniteHull` over the signed labels at the fixed procession `n`
(the packet label type of `ThetaPacketBridge`), available exactly under the finiteness
input: per-label volumes are the singleton point log-volumes of the actual theta-pilot
points of the hull at `n`. -/
def sourceThetaPilotFiniteHull (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) (hfin : I.sourceHullVolume v R n < ⊤) :
    FiniteHull (SignedLabel l.value) where
  volume := fun j =>
    (I.sourcePointVolume v (I.sourceThetaPilotPoint v R n j)).toReal
  hullVolume := I.sourceRealHullVolume v R n
  contains := by
    intro j
    have hmem : I.sourceThetaPilotPoint v R n j ∈
        (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) :=
      I.sourceThetaPilotPoint_mem_sourceHolomorphicHull v R n j
    have hsub : ({I.sourceThetaPilotPoint v R n j} :
        Set (I.ThetaPilotPoint v)) ⊆
        (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) := by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hmem
    have h1 : I.sourcePointVolume v (I.sourceThetaPilotPoint v R n j) ≤
        I.sourceSetVolume v ({I.sourceThetaPilotPoint v R n j} :
          Set (I.ThetaPilotPoint v)) := by
      unfold sourceSetVolume
      exact le_iSup_of_le (I.sourceThetaPilotPoint v R n j)
        (le_iSup_of_le (Set.mem_singleton (I.sourceThetaPilotPoint v R n j))
          le_rfl)
    exact ENNReal.toReal_mono (ne_top_of_lt hfin)
      (le_trans h1 (I.sourceSetVolume_mono v hsub))

/-- **Interface-correction lemma (family 3).**  The negativity of the
procession-normalized lower bound (the consumer's `q < 0` slot) is exactly the packet
contraction condition `thetaValueAt < 1` at the chosen label; `0 < thetaValueAt` is the
only sign information available from `OriginalInput`. -/
theorem sourceThetaValue_neg_iff (n : ThetaPilotCarrier l)
    (j : SignedLabel l.value) :
    (Fintype.card (SourceVolumeIndex l) : ℝ) *
        Real.log (I.thetaValueAt (n.val : Int) 0 j) < 0 ↔
      I.thetaValueAt (n.val : Int) 0 j < 1 := by
  have hcard : (0 : ℝ) < (Fintype.card (SourceVolumeIndex l) : ℝ) := by
    exact_mod_cast sourceVolumeIndex_card_pos l
  have hpos : 0 < I.thetaValueAt (n.val : Int) 0 j :=
    I.thetaValueAt_pos (n.val) 0 j
  rw [mul_neg_iff, Real.log_neg_iff hpos]
  constructor
  · rintro (⟨_, h⟩ | ⟨h, _⟩)
    · exact h
    · exact absurd h (not_lt_of_ge hcard.le)
  · intro h
    exact Or.inl ⟨hcard, h⟩

/-- The theta special values entering the normalized bound are the one-column ledger
scales of `SourceSharedBoundary` (source transport of the shared boundary). -/
theorem thetaValueAt_eq_oneColumnScale (m : Int) (j : SignedLabel l.value) :
    I.thetaValueAt m 0 j = I.oneColumnScale m j :=
  I.linkAt_scale m 0 1 m j

/-- **ThetaPacketBridge link.**  The theta special values of the normalized lower bound
are, along the one-column ledger, the positive-packet scales of
`FiniteThetaPacket.toPositivePacket`. -/
theorem thetaValueAt_eq_toPositivePacket_scale (m : Int)
    (j : SignedLabel l.value) :
    I.thetaValueAt m 0 j = (I.oneColumnPacket m).toPositivePacket.scale j :=
  (I.thetaValueAt_eq_oneColumnScale m j).trans (by simp [oneColumnScale])

end OriginalInput
end Theorem311Source

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for the wiring of the hull log-volume interface into the Step-XI
finite-certificate consumer. -/
def certificateHullWiring : Obligation :=
  { id := "IUT-III.corollary-3.12-step-XI-certificate-hull-wiring"
    source :=
      "IUT III, Corollary 3.12, Step (xi): FiniteCertificateBridge consumer fed " ++
        "by the hull log-volume interface"
    status := VerificationStatus.interface
    note :=
      "Discharged from an interface realization W (plus a finite labeling into " ++
        "the image union and WeightedValues bookkeeping): the FiniteHull with " ++
        "hullVolume = real part of the hull log-volume (iqHullFiniteHull), the " ++
        "WeightedValues average bound (iqHullFiniteHull_average_le), the full " ++
        "StepXIFiniteCertificate (iqHullCertificate), FiniteStepXILinkEvidence " ++
        "with targetSigned = real hull volume (iqHullLinkEvidence), and hence " ++
        "Cor312Conclusion via the existing FiniteCertificateBridge assembly " ++
        "(iqHullCor312Conclusion). " ++
        "Still supplied hypotheses, never derived: the realization W itself; the " ++
        "interface-level bounds ofReal q <= logVolume imageSet and logVolume hull " ++
        "<= ofReal theta; 0 <= theta; q < 0; the IPL/SHE/APT evidence. " ++
        "Interface-correction lemmas: iqHullRealVolume_le_theta_iff shows the " ++
        "consumer's real upper-bound field is exactly an interface ENNReal bound " ++
        "(finiteness alone does not supply it); at the value level " ++
        "sourceThetaBound_unsat_of_degreeFaithful proves such a real bound is " ++
        "unsatisfiable under pointwise degree faithfulness, and " ++
        "sourceThetaValue_neg_iff identifies the q < 0 slot with thetaValueAt < 1 " ++
        "(the contraction input q_contracting, not available from OriginalInput). " ++
        "Value-level wiring: sourceRealHullVolume_ge_normalized, " ++
        "sourceThetaPilotFiniteHull, and the one-column packet-scale transport " ++
        "thetaValueAt_eq_toPositivePacket_scale. A Haar-contraction FiniteHull " ++
        "witness (haarContractionFiniteHull) shows the wiring is non-vacuous. " ++
        "NOT proved: a realization of the interface for the actual source carrier."
    dependsOn :=
      [ "IUT-III.corollary-3.12-iq-hull-interface-discharge",
        "IUT-III.finite-certificate-to-contract",
        "IUT-III.holomorphic-hull-determinant-log-volume",
        "IUT-III.StepXI.finite-theta-packet-bridge" ] }

end LeanFormal.IUT.Audit
