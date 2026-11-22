import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealSignedLogVolume
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.OModuleCompactnessLayer
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealFinitePhaseGate
import LeanFormal.IUT.Audit.Status

/-!
# Actual signed q-pilot carrier and the (xi-f) comparison (deep-audit group C)

This file attacks the first missing object of the Card-HULLREAL signed q-pilot
comparison recorded in coord/DEEP_AUDIT_ABC_IUT.md section 3.3 / item 4:

1. an actual qSigned equal to the q-pilot signed log-volume (not an arbitrary
   real parameter);
2. the corpus (xi-f) comparison qSigned <= -|log Theta|;
3. a non-collapsed finite hull, or an ambient O-module carrier.

The signed wrapper CardHullRealSignedLogVolume.lean leaves qSigned free in
SourceXifSignedComparison and in sourceSignedHullCertificate.  This file fixes
the actual q-pilot value from the source theta packet and reduces the comparison
exactly.

## Actual q-pilot value

The source q-parameter is the actual positive real q of the theta packet
(I.theaterAt 0 0).thetaPacket (IUT II theta special values).  The value-layer
q-pilot signed log-volume is

  sourceQPilotSignedLog v R = -|Real.log q|,

the negative absolute log-degree of the realized q-parameter
(sourceQPilotSignedLog_eq_neg_abs_logDegree, using the realization field
degree_of_q).  This is the corpus -|log(q)| (III:10843-10848) and is a
definition, not a parameter: no certificate below takes qSigned as an input.

## Relation to the arithmetic q-family

The tree also has an actual finite-place arithmetic q-pilot signed log,
ArithmeticQPilotGlobalNormalization.absoluteDegreeNormalizedLowerSignedLog, on a
number field k.  That quantity lives on a different carrier (finite places and
q-candidates) from the source theta-packet value layer; no theorem in the tree
identifies it with sourceQPilotSignedLog.  The comparison here uses the source
theta-packet quantity -|log q|, which is the corpus q-parameter log at the
source.  Supplying the number-field identification is a separate missing bridge
and is not assumed.

## Exact reduction and unconditional collapse

Without any finiteness hypothesis the signed comparison at the actual q-pilot is
definitionally equivalent to

  sourceRealHullVolume v R n <= |Real.log q|

(sourceXifSignedComparisonAtQPilot_iff_realPart_le).

The value-realized hull, however, is *unconditionally collapsed*.  The source
holomorphic hull is a submonoid of the value carrier and the log-degree is
additive; a positive-degree hull point has arbitrarily large powers in the hull,
so either the hull volume is top or every hull log-degree is nonpositive.  In
both phases the real hull log-volume is zero (sourceRealHullVolume_eq_zero; the
two-phase dichotomy is sourceHullVolume_eq_top_iff_exists_pos_logDegree /
sourceHullVolume_lt_top_iff_forall_logDegree_nonpos from
CardHullRealFinitePhaseGate.lean).  Hence:

* sourceSignedHullLogVolume v R n = 0 unconditionally
  (sourceSignedHullLogVolume_eq_zero);
* the literal (xi-f) comparison is unconditionally true for every source q
  (sourceXifSignedComparisonAtQPilot_unconditional);
* the non-collapsed carrier SourceSignedQPilotCarrier is empty for every
  realization (not_nonempty_sourceSignedQPilotCarrier), and the q-scale hull
  bound SourceQPilotHullBound is equivalent to sourceHullVolume = 0, not to a
  positive finite bound (sourceQPilotHullBound_iff_hullVolume_eq_zero).

The ENNReal form sourceHullVolume <= ofReal |log q| is equivalent to the signed
comparison only under finiteness
(sourceXifSignedComparisonAtQPilot_iff_hullVolume_le), and finiteness forces
the zero phase.  This is the precise sense in which the literal (xi-f)
comparison closes degenerately: the signed hull carrier is *always* zero at the
value realization, so the comparison has zero discriminating power there.  The
earlier degree-faithful and contracted-generator degeneracies
(sourceXifSignedComparisonAtQPilot_degenerate_of_degreeFaithful,
sourceXifSignedComparisonAtQPilot_of_contractedGenerators) are special cases of
this unconditional collapse.

## The exact missing object

The missing object is therefore not a numeric bound at the value layer (the
value hull cannot have a positive finite log-volume at all).  It is an ambient
carrier in which the holomorphic hull is not the least value-monoid submonoid:
the paper's IQ(S+-_{j+1}; n,circ D^vdash_{vQ}) with its ring-of-integers /
O-module structure and Haar log-volume.  The candidate interface
SourceSignedQPilotCarrier records exactly what such a carrier must supply at the
signed q-pilot:

  q < 1,  0 < sourceRealHullVolume,  forall hull x, ld x <= |log q|,

and Nonempty of it is equivalent to positivity plus the signed comparison
(nonempty_sourceSignedQPilotCarrier_iff_comparison_and_positivity).  At the
value realization this interface is provably empty; the consumer wiring
(sourceSignedQPilotCertificate, sourceSignedQPilotCor312Conclusion) is a valid
conditional assembly but cannot be instantiated on sourceHolomorphicHull.

For the ambient O-module route, the value-level sufficient condition is the
scaled region hull subset lam . O with O-degree bound C and the numeric
normalization ld(lam) + C <= |log q|
(sourceQPilotHullBound_of_scaledRegion,
sourceQPilotHullBound_of_oneCircUCompactness,
sourceQPilotHullBound_of_unitRegionHaarData).  At a tight hull point the
normalization is also necessary
(sourceLocalLogDegree_add_le_qPilotMagnitude_of_qPilotHullBound).  But this
route still has to be run on a carrier where the hull is not the value
submonoid; at the value layer the bound collapses to zero
(sourceQPilotHullBound_iff_hullVolume_eq_zero).

## Honesty boundary

Nothing here constructs the paper's IQ/O-module carrier, the compactness of
1,circ U, or a non-degree-faithful realization.  The value-layer collapse is
proved, not assumed; the non-collapsed carrier and the signed certificate are
conditional interfaces, and the certificate consumer theorem is not claimed to
have a value-layer inhabitant.  No sorry, axiom, placeholder, True, or
arbitrary qSigned is introduced.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT

noncomputable section

universe ua uv upi umon ui

namespace Theorem311Source
namespace OriginalInput

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-! ## 1. The actual q-pilot signed log -/

/-- The source q-parameter of the theta packet at the origin. -/
def sourceThetaPacketQ : Real :=
  (I.theaterAt 0 0).thetaPacket.q

/-- The q-pilot log magnitude |log(q)| of the actual source theta packet.  The
realization argument is carried only so that the q-pilot value lives on the same
carrier as the signed hull volume; the value itself is input data. -/
def sourceQPilotLogMagnitude (v : V) (R : I.SourceImageRealization v) : Real :=
  |Real.log I.sourceThetaPacketQ|

/-- The actual q-pilot signed log-volume -|log(q)| of the source theta packet:
the corpus left-hand side (III:10843-10848). -/
def sourceQPilotSignedLog (v : V) (R : I.SourceImageRealization v) : Real :=
  -I.sourceQPilotLogMagnitude v R

theorem sourceThetaPacketQ_pos : 0 < I.sourceThetaPacketQ :=
  (I.theaterAt 0 0).thetaPacket.q_pos

theorem sourceQPilotLogMagnitude_nonneg (v : V) (R : I.SourceImageRealization v) :
    0 <= I.sourceQPilotLogMagnitude v R :=
  abs_nonneg _

theorem sourceQPilotSignedLog_nonpos (v : V) (R : I.SourceImageRealization v) :
    I.sourceQPilotSignedLog v R <= 0 :=
  neg_nonpos.mpr (I.sourceQPilotLogMagnitude_nonneg v R)

theorem sourceQPilotLogMagnitude_pos_of_q_ne_one (v : V)
    (R : I.SourceImageRealization v) (hq1 : I.sourceThetaPacketQ ≠ 1) :
    0 < I.sourceQPilotLogMagnitude v R := by
  unfold sourceQPilotLogMagnitude
  rw [abs_pos]
  exact Real.log_ne_zero_of_pos_of_ne_one I.sourceThetaPacketQ_pos hq1

theorem sourceQPilotSignedLog_neg_of_q_ne_one (v : V)
    (R : I.SourceImageRealization v) (hq1 : I.sourceThetaPacketQ ≠ 1) :
    I.sourceQPilotSignedLog v R < 0 :=
  neg_neg_of_pos (I.sourceQPilotLogMagnitude_pos_of_q_ne_one v R hq1)

theorem sourceQPilotSignedLog_eq_log_of_q_lt_one (v : V)
    (R : I.SourceImageRealization v) (hq : I.sourceThetaPacketQ < 1) :
    I.sourceQPilotSignedLog v R = Real.log I.sourceThetaPacketQ := by
  unfold sourceQPilotSignedLog sourceQPilotLogMagnitude
  rw [abs_of_neg ((Real.log_neg_iff I.sourceThetaPacketQ_pos).mpr hq), neg_neg]

/-- The actual q-pilot signed log is the negative absolute log-degree of the
actual realized q-parameter (the degree_of_q field of the source realization). -/
theorem sourceQPilotLogMagnitude_eq_abs_logDegree (v : V)
    (R : I.SourceImageRealization v) :
    I.sourceQPilotLogMagnitude v R =
      |I.logDegreeAt 0 0 v (R.posRealAction
        (Multiplicative.ofAdd (Real.log I.sourceThetaPacketQ)))| := by
  unfold sourceQPilotLogMagnitude sourceThetaPacketQ
  rw [R.degree_of_q]

theorem sourceQPilotSignedLog_eq_neg_abs_logDegree (v : V)
    (R : I.SourceImageRealization v) :
    I.sourceQPilotSignedLog v R =
      -|I.logDegreeAt 0 0 v (R.posRealAction
        (Multiplicative.ofAdd (Real.log I.sourceThetaPacketQ)))| := by
  unfold sourceQPilotSignedLog
  rw [I.sourceQPilotLogMagnitude_eq_abs_logDegree]

/-- The q-pilot signed log is strictly negative exactly when the source q is not
the neutral value 1.  This pins the q-sign to the actual source packet. -/
theorem sourceQPilotSignedLog_neg_iff (v : V) (R : I.SourceImageRealization v) :
    I.sourceQPilotSignedLog v R < 0 ↔ I.sourceThetaPacketQ ≠ 1 := by
  constructor
  · intro h hq
    have h0 : I.sourceQPilotSignedLog v R = 0 := by
      unfold sourceQPilotSignedLog sourceQPilotLogMagnitude
      rw [hq, Real.log_one, abs_zero, neg_zero]
    rw [h0] at h
    exact lt_irrefl 0 h
  · exact I.sourceQPilotSignedLog_neg_of_q_ne_one v R

/-- In the contracted regime q < 1 the actual q is recovered from the q-pilot
signed log by exponentiation. -/
theorem sourceQPilotSignedLog_exp_of_q_lt_one (v : V)
    (R : I.SourceImageRealization v) (hq : I.sourceThetaPacketQ < 1) :
    Real.exp (I.sourceQPilotSignedLog v R) = I.sourceThetaPacketQ := by
  rw [I.sourceQPilotSignedLog_eq_log_of_q_lt_one v R hq]
  exact Real.exp_log I.sourceThetaPacketQ_pos

/-! ## 2. The (xi-f) comparison at the actual q-pilot -/

/-- The corpus (xi-f) comparison -|log(q)| <= -|log(Theta)| at the actual source
q-pilot, with the signed hull carrier -|log(Theta)| = sourceSignedHullLogVolume. -/
def SourceXifSignedComparisonAtQPilot (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) : Prop :=
  I.sourceQPilotSignedLog v R <= I.sourceSignedHullLogVolume v R n

/-- Corpus-shaped form: -|log(q)| <= -|log(Theta)| with -|log(Theta)| the
negative real hull log-volume. -/
theorem sourceXifSignedComparisonAtQPilot_iff_corpus (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    I.SourceXifSignedComparisonAtQPilot v R n ↔
      -|Real.log I.sourceThetaPacketQ| <=
        -I.sourceRealHullVolume v R n :=
  Iff.rfl

/-- **Exact reduction, unconditional.**  The signed comparison at the actual
q-pilot is exactly the real-part bound sourceRealHullVolume <= |log q|.  No
finiteness is used: when the hull volume is top its real part is 0 and the
comparison is automatic. -/
theorem sourceXifSignedComparisonAtQPilot_iff_realPart_le (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    I.SourceXifSignedComparisonAtQPilot v R n ↔
      I.sourceRealHullVolume v R n <= I.sourceQPilotLogMagnitude v R := by
  unfold SourceXifSignedComparisonAtQPilot sourceQPilotSignedLog
    sourceSignedHullLogVolume
  exact neg_le_neg_iff

/-- Under finiteness, the signed comparison is exactly the ENNReal hull upper
bound sourceHullVolume <= ofReal |log q|. -/
theorem sourceXifSignedComparisonAtQPilot_iff_hullVolume_le (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hfin : I.sourceHullVolume v R n < ⊤) :
    I.SourceXifSignedComparisonAtQPilot v R n ↔
      I.sourceHullVolume v R n <= ENNReal.ofReal (I.sourceQPilotLogMagnitude v R) := by
  rw [I.sourceXifSignedComparisonAtQPilot_iff_realPart_le]
  constructor
  · intro h
    calc I.sourceHullVolume v R n =
          ENNReal.ofReal (I.sourceRealHullVolume v R n) :=
        I.sourceHullVolume_eq_ofReal v R n hfin
      _ <= ENNReal.ofReal (I.sourceQPilotLogMagnitude v R) :=
        ENNReal.ofReal_le_ofReal h
  · intro h
    exact toReal_le_of_le_ofReal (I.sourceQPilotLogMagnitude_nonneg v R) h

/-- The genuine finite q-scale bound implies finiteness of the hull. -/
theorem sourceHullVolume_lt_top_of_le_ofReal_qPilotMagnitude (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (h : I.sourceHullVolume v R n <= ENNReal.ofReal (I.sourceQPilotLogMagnitude v R)) :
    I.sourceHullVolume v R n < ⊤ :=
  lt_of_le_of_lt h ENNReal.ofReal_lt_top

/-- **Degeneracy of the literal (xi-f) comparison, positive half.**  Under
pointwise degree faithfulness the signed hull volume collapses to 0, so the
comparison holds for every source q with q != 1, without any hull estimate. -/
theorem sourceXifSignedComparisonAtQPilot_of_degreeFaithful (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hdeg : ∀ b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b)
    (hq1 : I.sourceThetaPacketQ ≠ 1) :
    I.SourceXifSignedComparisonAtQPilot v R n := by
  unfold SourceXifSignedComparisonAtQPilot
  rw [sourceSignedHullLogVolume_eq_zero_of_degreeFaithful I v R n hdeg]
  exact le_of_lt (I.sourceQPilotSignedLog_neg_of_q_ne_one v R hq1)

/-- **Degeneracy of the literal (xi-f) comparison, negative half.**  Under
pointwise degree faithfulness the genuine finite q-scale hull bound is false. -/
theorem not_sourceHullVolume_le_ofReal_qPilotMagnitude_of_degreeFaithful (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hdeg : ∀ b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    ¬ I.sourceHullVolume v R n <= ENNReal.ofReal (I.sourceQPilotLogMagnitude v R) := by
  intro h
  rw [I.sourceHullVolume_eq_top_of_degreeFaithful v R n hdeg] at h
  exact not_le_of_gt ENNReal.ofReal_lt_top h

/-- **Why the literal (xi-f) comparison closes degenerately.**  Under pointwise
degree faithfulness the signed comparison holds (positive half) while the
finite q-scale hull bound fails (negative half).  Hence the comparison alone,
without finiteness, has no discriminating power at the collapsed carrier. -/
theorem sourceXifSignedComparisonAtQPilot_degenerate_of_degreeFaithful (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hdeg : ∀ b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b)
    (hq1 : I.sourceThetaPacketQ ≠ 1) :
    I.SourceXifSignedComparisonAtQPilot v R n ∧
      ¬ I.sourceHullVolume v R n <= ENNReal.ofReal (I.sourceQPilotLogMagnitude v R) :=
  ⟨I.sourceXifSignedComparisonAtQPilot_of_degreeFaithful v R n hdeg hq1,
    I.not_sourceHullVolume_le_ofReal_qPilotMagnitude_of_degreeFaithful v R n hdeg⟩

/-! ## 3. The exact q-scale hull bound and the non-collapsed carrier -/

/-- The candidate q-scale hull bound: every hull point has log-degree at most
the actual q-pilot magnitude |log q|.  This is the exact missing analytic field;
it is not supplied by the source input. -/
structure SourceQPilotHullBound (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) : Prop where
  hull_logDegree_le_qPilot :
    ∀ x : I.ThetaPilotPoint v,
      x ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) ->
        I.sourceLocalLogDegree v x <= I.sourceQPilotLogMagnitude v R

/-- The q-scale hull bound is exactly the finite ENNReal hull bound
sourceHullVolume <= ofReal |log q|. -/
theorem sourceQPilotHullBound_iff (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) :
    I.SourceQPilotHullBound v R n ↔
      I.sourceHullVolume v R n <= ENNReal.ofReal (I.sourceQPilotLogMagnitude v R) := by
  constructor
  · intro B
    unfold sourceHullVolume sourceSetVolume
    exact iSup_le fun x => iSup_le fun hx =>
      ENNReal.ofReal_le_ofReal (B.hull_logDegree_le_qPilot x hx)
  · intro h
    refine ⟨fun x hx => ?_⟩
    have h1 : ENNReal.ofReal (I.sourceLocalLogDegree v x) <= I.sourceHullVolume v R n := by
      unfold sourceHullVolume sourceSetVolume
      exact le_iSup_of_le x (le_iSup_of_le hx le_rfl)
    exact (ENNReal.ofReal_le_ofReal_iff (I.sourceQPilotLogMagnitude_nonneg v R)).mp
      (le_trans h1 h)

/-- The q-scale bound is exactly the hull finiteness together with the literal
(xi-f) signed comparison. -/
theorem sourceQPilotHullBound_iff_comparison_and_finite (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    I.SourceQPilotHullBound v R n ↔
      (I.sourceHullVolume v R n < ⊤ ∧ I.SourceXifSignedComparisonAtQPilot v R n) := by
  constructor
  · intro B
    have hb : I.sourceHullVolume v R n <= ENNReal.ofReal (I.sourceQPilotLogMagnitude v R) :=
      (I.sourceQPilotHullBound_iff v R n).mp B
    have hfin : I.sourceHullVolume v R n < ⊤ :=
      lt_of_le_of_lt hb ENNReal.ofReal_lt_top
    exact ⟨hfin,
      (I.sourceXifSignedComparisonAtQPilot_iff_hullVolume_le v R n hfin).mpr hb⟩
  · rintro ⟨hfin, hcomp⟩
    exact (I.sourceQPilotHullBound_iff v R n).mpr
      ((I.sourceXifSignedComparisonAtQPilot_iff_hullVolume_le v R n hfin).mp hcomp)


/-- The log-degree of a power of a global value point, with the additive law. -/
theorem sourceLocalLogDegree_pow_mul (v : V)
    (s x : I.ThetaPilotPoint v) (k : ℕ) :
    I.sourceLocalLogDegree v (s ^ k * x) =
      (k : ℝ) * I.sourceLocalLogDegree v s + I.sourceLocalLogDegree v x := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', mul_assoc, I.sourceLocalLogDegree_mul, ih]
      push_cast
      ring

/-- **The q-scale hull bound forces every hull scaling to be nonpositive.**
Otherwise iterating a positive-degree scaling multiplies a hull point's
log-degree without bound, contradicting the bound.  This is the exact
degree-level consequence of the q-scale bound: every positive-degree point of
the hull must come from the theta images, not from the scaling action. -/
theorem sourceScaling_logDegree_nonpos_of_qPilotHullBound (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (B : I.SourceQPilotHullBound v R n)
    {s : I.ThetaPilotPoint v} (hs : s ∈ I.sourceScalingUnits v) :
    I.sourceLocalLogDegree v s <= 0 := by
  by_contra hnonpos
  have hpos : 0 < I.sourceLocalLogDegree v s := not_le.mp hnonpos
  let x0 : I.ThetaPilotPoint v :=
    I.sourceThetaPilotPoint v R n (zeroSignedLabel (l := l))
  have hx0 : x0 ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) :=
    I.sourceThetaPilotPoint_mem_sourceHolomorphicHull v R n (zeroSignedLabel (l := l))
  have hmem : ∀ k : ℕ,
      s ^ k * x0 ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) := by
    intro k
    induction k with
    | zero => simpa using hx0
    | succ k ih =>
        rw [pow_succ', mul_assoc]
        exact I.sourceHolomorphicHull_scaling_mem v R n hs ih
  obtain ⟨k, hk⟩ := exists_nat_gt ((I.sourceQPilotLogMagnitude v R -
    I.sourceLocalLogDegree v x0) / I.sourceLocalLogDegree v s)
  have hk' : I.sourceQPilotLogMagnitude v R - I.sourceLocalLogDegree v x0 <
      (k : ℝ) * I.sourceLocalLogDegree v s :=
    (div_lt_iff₀ hpos).mp hk
  have hbound := B.hull_logDegree_le_qPilot (s ^ k * x0) (hmem k)
  rw [I.sourceLocalLogDegree_pow_mul v s x0 k] at hbound
  linarith

/-- Positivity of the real hull log-volume implies finiteness of the hull volume:
if the hull volume were top, its real part would be 0. -/
theorem sourceHullVolume_lt_top_of_sourceRealHullVolume_pos (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hpos : 0 < I.sourceRealHullVolume v R n) :
    I.sourceHullVolume v R n < ⊤ := by
  by_contra hfin
  have htop : I.sourceHullVolume v R n = ⊤ := by
    rcases eq_or_lt_of_le (le_top : I.sourceHullVolume v R n <= ⊤) with h | h
    · exact h
    · exact absurd h hfin
  have hpos' := hpos
  unfold sourceRealHullVolume at hpos'
  rw [htop, ENNReal.toReal_top] at hpos'
  exact lt_irrefl 0 hpos'

/-- The non-collapsed signed q-pilot carrier: the actual q is contracted
(q < 1), the paper's WLOG branch -|log Theta| < 0 holds (positive real hull
volume), and the hull log-degree is bounded at the actual q-pilot magnitude.
The q-value is fixed by the source (sourceQPilotSignedLog), not a field. -/
structure SourceSignedQPilotCarrier (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) : Prop where
  q_lt_one : I.sourceThetaPacketQ < 1
  hull_realVolume_pos : 0 < I.sourceRealHullVolume v R n
  hull_logDegree_le_qPilot :
    ∀ x : I.ThetaPilotPoint v,
      x ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) ->
        I.sourceLocalLogDegree v x <= I.sourceQPilotLogMagnitude v R

theorem sourceSignedQPilotCarrier_hullBound (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (K : I.SourceSignedQPilotCarrier v R n) :
    I.SourceQPilotHullBound v R n :=
  ⟨K.hull_logDegree_le_qPilot⟩

theorem sourceSignedQPilotCarrier_hullVolume_lt_top (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (K : I.SourceSignedQPilotCarrier v R n) :
    I.sourceHullVolume v R n < ⊤ :=
  I.sourceHullVolume_lt_top_of_sourceRealHullVolume_pos v R n
    K.hull_realVolume_pos

theorem sourceSignedQPilotCarrier_signedHull_neg (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (K : I.SourceSignedQPilotCarrier v R n) :
    I.sourceSignedHullLogVolume v R n < 0 := by
  unfold sourceSignedHullLogVolume
  exact neg_neg_of_pos K.hull_realVolume_pos

theorem sourceSignedQPilotCarrier_qPilot_neg (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (K : I.SourceSignedQPilotCarrier v R n) :
    I.sourceQPilotSignedLog v R < 0 :=
  I.sourceQPilotSignedLog_neg_of_q_ne_one v R (ne_of_lt K.q_lt_one)

theorem sourceSignedQPilotCarrier_comparison (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (K : I.SourceSignedQPilotCarrier v R n) :
    I.SourceXifSignedComparisonAtQPilot v R n := by
  have hb : I.sourceHullVolume v R n <=
      ENNReal.ofReal (I.sourceQPilotLogMagnitude v R) :=
    (I.sourceQPilotHullBound_iff v R n).mp
      (I.sourceSignedQPilotCarrier_hullBound v R n K)
  exact (I.sourceXifSignedComparisonAtQPilot_iff_realPart_le v R n).mpr
    (toReal_le_of_le_ofReal (I.sourceQPilotLogMagnitude_nonneg v R) hb)

theorem sourceSignedQPilotCarrier_realVolume_le_qPilotMagnitude (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (K : I.SourceSignedQPilotCarrier v R n) :
    I.sourceRealHullVolume v R n <= I.sourceQPilotLogMagnitude v R :=
  (I.sourceXifSignedComparisonAtQPilot_iff_realPart_le v R n).mp
    (I.sourceSignedQPilotCarrier_comparison v R n K)

/-- Exact characterization of the non-collapsed carrier structure. -/
theorem nonempty_sourceSignedQPilotCarrier_iff (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    Nonempty (I.SourceSignedQPilotCarrier v R n) ↔
      (I.sourceThetaPacketQ < 1 ∧ 0 < I.sourceRealHullVolume v R n ∧
        I.SourceQPilotHullBound v R n) := by
  constructor
  · rintro ⟨K⟩
    exact ⟨K.q_lt_one, K.hull_realVolume_pos,
      I.sourceSignedQPilotCarrier_hullBound v R n K⟩
  · rintro ⟨hq, hpos, B⟩
    exact ⟨⟨hq, hpos, B.hull_logDegree_le_qPilot⟩⟩

/-- **Exact characterization of the non-collapsed signed q-pilot comparison.**
At the contracted source q, the carrier exists exactly when the hull real
log-volume is positive (the paper's WLOG branch -|log Theta| < 0) and the
literal (xi-f) signed comparison holds.  Positivity supplies finiteness, so the
signed comparison here is the genuine q-scale bound, not the degenerate
top-carrier form. -/
theorem nonempty_sourceSignedQPilotCarrier_iff_comparison_and_positivity
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hq : I.sourceThetaPacketQ < 1) :
    Nonempty (I.SourceSignedQPilotCarrier v R n) ↔
      (0 < I.sourceRealHullVolume v R n ∧ I.SourceXifSignedComparisonAtQPilot v R n) := by
  constructor
  · rintro ⟨K⟩
    exact ⟨K.hull_realVolume_pos,
      I.sourceSignedQPilotCarrier_comparison v R n K⟩
  · rintro ⟨hpos, hcomp⟩
    have hfin : I.sourceHullVolume v R n < ⊤ :=
      I.sourceHullVolume_lt_top_of_sourceRealHullVolume_pos v R n hpos
    have hb : I.sourceHullVolume v R n <=
        ENNReal.ofReal (I.sourceQPilotLogMagnitude v R) :=
      (I.sourceXifSignedComparisonAtQPilot_iff_hullVolume_le v R n hfin).mp hcomp
    exact ⟨hq, hpos, ((I.sourceQPilotHullBound_iff v R n).mpr hb).hull_logDegree_le_qPilot⟩

/-- Under pointwise degree faithfulness the non-collapsed carrier is empty: the
hull volume is top and its real part is 0, contradicting positivity. -/
theorem not_nonempty_sourceSignedQPilotCarrier_of_degreeFaithful (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hdeg : ∀ b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    ¬ Nonempty (I.SourceSignedQPilotCarrier v R n) := by
  rintro ⟨K⟩
  have hpos := K.hull_realVolume_pos
  unfold sourceRealHullVolume at hpos
  rw [I.sourceHullVolume_eq_top_of_degreeFaithful v R n hdeg,
    ENNReal.toReal_top] at hpos
  exact lt_irrefl 0 hpos

/-- Whenever the real hull log-volume is zero the literal (xi-f) comparison holds
for every source q: this covers both the degree-faithful top carrier and the
fully contracted nonpositive hull, and records the exact degeneracy. -/
theorem sourceXifSignedComparisonAtQPilot_of_realVolume_eq_zero (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (h0 : I.sourceRealHullVolume v R n = 0) :
    I.SourceXifSignedComparisonAtQPilot v R n := by
  rw [I.sourceXifSignedComparisonAtQPilot_iff_realPart_le, h0]
  exact I.sourceQPilotLogMagnitude_nonneg v R

/-- Under the contracted (nonpositive hull) route the real hull log-volume is
zero: the finite hull is the collapsed signed carrier, not a non-collapsed one. -/
theorem sourceRealHullVolume_eq_zero_of_contractedGenerators (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hImage : ∀ j : SignedLabel l.value,
      I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j) <= 0)
    (hScaling : ∀ s ∈ I.sourceScalingUnits v, I.sourceLocalLogDegree v s <= 0) :
    I.sourceRealHullVolume v R n = 0 := by
  have hle : I.sourceHullVolume v R n <= ENNReal.ofReal 0 := by
    unfold sourceHullVolume sourceSetVolume
    exact iSup_le fun x => iSup_le fun hx =>
      ENNReal.ofReal_le_ofReal
        (I.sourceHolomorphicHull_logDegree_nonpos_of_contractedGenerators
          v R n hImage hScaling x hx)
  unfold sourceRealHullVolume
  exact le_antisymm (toReal_le_of_le_ofReal le_rfl hle) ENNReal.toReal_nonneg

/-- Under the contracted route the signed hull log-volume is zero: the signed
carrier is collapsed even though the hull volume is finite. -/
theorem sourceSignedHullLogVolume_eq_zero_of_contractedGenerators (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hImage : ∀ j : SignedLabel l.value,
      I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j) <= 0)
    (hScaling : ∀ s ∈ I.sourceScalingUnits v, I.sourceLocalLogDegree v s <= 0) :
    I.sourceSignedHullLogVolume v R n = 0 := by
  unfold sourceSignedHullLogVolume
  rw [I.sourceRealHullVolume_eq_zero_of_contractedGenerators v R n hImage hScaling,
    neg_zero]

/-- The literal (xi-f) comparison is *provable* in the contracted regime, but
degenerately: the signed hull carrier is zero, so the comparison is the trivial
q <= 0 for every source q.  This is the finite counterpart of the
degree-faithful degeneracy. -/
theorem sourceXifSignedComparisonAtQPilot_of_contractedGenerators (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hImage : ∀ j : SignedLabel l.value,
      I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j) <= 0)
    (hScaling : ∀ s ∈ I.sourceScalingUnits v, I.sourceLocalLogDegree v s <= 0) :
    I.SourceXifSignedComparisonAtQPilot v R n :=
  I.sourceXifSignedComparisonAtQPilot_of_realVolume_eq_zero v R n
    (I.sourceRealHullVolume_eq_zero_of_contractedGenerators v R n hImage hScaling)

/-- Under the fully contracted (nonpositive hull) route the non-collapsed
carrier is empty: the hull volume is finite but its real part is 0, so the
signed comparison is again vacuous.  This is the finite counterpart of the
degree-faithful collapse. -/
theorem not_nonempty_sourceSignedQPilotCarrier_of_contractedGenerators (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hImage : ∀ j : SignedLabel l.value,
      I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j) <= 0)
    (hScaling : ∀ s ∈ I.sourceScalingUnits v, I.sourceLocalLogDegree v s <= 0) :
    ¬ Nonempty (I.SourceSignedQPilotCarrier v R n) := by
  rintro ⟨K⟩
  have hpos := K.hull_realVolume_pos
  rw [I.sourceRealHullVolume_eq_zero_of_contractedGenerators v R n hImage hScaling] at hpos
  exact lt_irrefl 0 hpos

/-! ## 4. The ambient O-module / scaled-region route and its exact residual -/

/-- **The exact numerical normalization of an ambient scaled-region carrier.**
If the hull is contained in lam . O, every point of O has log-degree at most C,
and ld(lam) + C <= |log q|, then the q-scale hull bound holds.  This numeric
inequality is the exact extra field needed on top of an O-module compactness or
unit-region datum. -/
theorem sourceQPilotHullBound_of_scaledRegion (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    {lam : I.ThetaPilotPoint v} {O : Set (I.ThetaPilotPoint v)} {C : Real}
    (hsub : (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) <=
      scaledRegionImage lam O)
    (hO : ∀ y ∈ O, I.sourceLocalLogDegree v y <= C)
    (hC : I.sourceLocalLogDegree v lam + C <= I.sourceQPilotLogMagnitude v R) :
    I.SourceQPilotHullBound v R n := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨y, hy, rfl⟩ := (mem_scaledRegionImage_iff).mp (hsub hx)
  rw [I.sourceLocalLogDegree_mul v lam y]
  exact le_trans (add_le_add le_rfl (hO y hy)) hC


/-- Converse at a tight hull point: if the scaled-region bound C is attained at
a point y of O whose scaling lam*y lies in the hull, then the q-scale hull bound
forces the numeric normalization ld(lam) + C <= |log q|.  Thus the residual
inequality is not an artifact of the sufficient direction; it is the exact
numeric content of the carrier at a tight point. -/
theorem sourceLocalLogDegree_add_le_qPilotMagnitude_of_qPilotHullBound (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (B : I.SourceQPilotHullBound v R n)
    {lam y : I.ThetaPilotPoint v} {C : Real}
    (hy : I.sourceLocalLogDegree v y = C)
    (hmem : lam * y ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v))) :
    I.sourceLocalLogDegree v lam + C <= I.sourceQPilotLogMagnitude v R := by
  have h := B.hull_logDegree_le_qPilot (lam * y) hmem
  rw [I.sourceLocalLogDegree_mul v lam y, hy] at h
  exact h

/-- The unit-region/Haar datum plus the q-pilot normalization of its degree
bound gives the q-scale hull bound. -/
theorem sourceQPilotHullBound_of_unitRegionHaarData (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n)
    (hC : I.sourceLocalLogDegree v D.scaling + D.degreeBound <=
      I.sourceQPilotLogMagnitude v R) :
    I.SourceQPilotHullBound v R n :=
  I.sourceQPilotHullBound_of_scaledRegion v R n
    (lam := D.scaling) (O := D.unitRegion) (C := D.degreeBound)
    D.hull_subset_scaledRegionImage D.unitRegion_logDegree_le hC

/-- The ambient O-module compactness datum plus the q-pilot normalization of its
degree bound gives the q-scale hull bound.  The compactness datum supplies the
containment hull subset lam . O and the bound C; it does not supply the numeric
inequality ld(lam) + C <= |log q|. -/
theorem sourceQPilotHullBound_of_oneCircUCompactness (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (K : I.SourceOneCircUCompactness v R n)
    (hC : I.sourceLocalLogDegree v K.scaling + K.layer.degreeBound <=
      I.sourceQPilotLogMagnitude v R) :
    I.SourceQPilotHullBound v R n :=
  I.sourceQPilotHullBound_of_scaledRegion v R n
    (lam := K.scaling) (O := K.layer.unitRegion) (C := K.layer.degreeBound)
    K.hull_subset_scaledRegionImage K.layer.unitRegion_logDegree_le hC

/-- The non-collapsed carrier from a scaled region, provided the region is
normalized at the q-pilot scale and the hull real log-volume is positive (the
non-collapse branch). -/
theorem sourceSignedQPilotCarrier_of_scaledRegion (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hq : I.sourceThetaPacketQ < 1)
    {lam : I.ThetaPilotPoint v} {O : Set (I.ThetaPilotPoint v)} {C : Real}
    (hsub : (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) <=
      scaledRegionImage lam O)
    (hO : ∀ y ∈ O, I.sourceLocalLogDegree v y <= C)
    (hC : I.sourceLocalLogDegree v lam + C <= I.sourceQPilotLogMagnitude v R)
    (hpos : 0 < I.sourceRealHullVolume v R n) :
    Nonempty (I.SourceSignedQPilotCarrier v R n) :=
  ⟨⟨hq, hpos,
    (I.sourceQPilotHullBound_of_scaledRegion v R n hsub hO hC).hull_logDegree_le_qPilot⟩⟩

/-- The non-collapsed carrier from the ambient O-module compactness datum plus
the exact normalization inequality and positivity. -/
theorem sourceSignedQPilotCarrier_of_oneCircUCompactness (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (K : I.SourceOneCircUCompactness v R n)
    (hq : I.sourceThetaPacketQ < 1)
    (hC : I.sourceLocalLogDegree v K.scaling + K.layer.degreeBound <=
      I.sourceQPilotLogMagnitude v R)
    (hpos : 0 < I.sourceRealHullVolume v R n) :
    Nonempty (I.SourceSignedQPilotCarrier v R n) :=
  ⟨⟨hq, hpos,
    (I.sourceQPilotHullBound_of_oneCircUCompactness v R n K hC).hull_logDegree_le_qPilot⟩⟩

/-! ## 5. The non-collapse boundary and consumer wiring -/

/-- The paper's WLOG branch: positive real hull log-volume is exactly negative
signed hull log-volume, i.e. -|log Theta| < 0. -/
theorem sourceRealHullVolume_pos_iff_signedHull_neg (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    0 < I.sourceRealHullVolume v R n ↔ I.sourceSignedHullLogVolume v R n < 0 := by
  unfold sourceSignedHullLogVolume
  exact (neg_lt_zero).symm

/-- The comparison has content exactly when the real hull log-volume exceeds the
q-pilot magnitude; it fails as soon as that bound is violated. -/
theorem not_sourceXifSignedComparisonAtQPilot_of_realVolume_gt (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (h : I.sourceQPilotLogMagnitude v R < I.sourceRealHullVolume v R n) :
    ¬ I.SourceXifSignedComparisonAtQPilot v R n := by
  rw [I.sourceXifSignedComparisonAtQPilot_iff_realPart_le]
  exact not_le_of_gt h

/-- The non-collapsed carrier places both sides of the signed comparison
strictly below zero: the corpus sign regime -|log q| < 0 > -|log Theta|. -/
theorem sourceSignedQPilotCarrier_both_negative (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (K : I.SourceSignedQPilotCarrier v R n) :
    I.sourceQPilotSignedLog v R < 0 ∧ I.sourceSignedHullLogVolume v R n < 0 :=
  ⟨I.sourceSignedQPilotCarrier_qPilot_neg v R n K,
    I.sourceSignedQPilotCarrier_signedHull_neg v R n K⟩

/-- The faithful signed certificate at the actual q-pilot, constructed from the
non-collapsed carrier.  The qSigned slot is the source q-pilot signed log (a
definition), not a free parameter. -/
def sourceSignedQPilotCertificate (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) (K : I.SourceSignedQPilotCarrier v R n) :
    StepXIFiniteCertificate (SignedLabel l.value) :=
  I.sourceSignedHullCertificate v R n (I.sourceQPilotSignedLog v R)
    (I.sourceSignedQPilotCarrier_comparison v R n K)
    (I.sourceSignedQPilotCarrier_qPilot_neg v R n K)

/-- The certificate's qSigned is the actual q-pilot signed log. -/
theorem sourceSignedQPilotCertificate_qSigned (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (K : I.SourceSignedQPilotCarrier v R n) :
    (I.sourceSignedQPilotCertificate v R n K).qSigned = I.sourceQPilotSignedLog v R :=
  rfl

/-- The certificate's thetaSigned is the zero cap on the signed surface. -/
theorem sourceSignedQPilotCertificate_thetaSigned (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (K : I.SourceSignedQPilotCarrier v R n) :
    (I.sourceSignedQPilotCertificate v R n K).thetaSigned = 0 :=
  rfl

/-- The certificate's hull comparison is exactly the corpus (xi-f) comparison at
the actual q-pilot. -/
theorem sourceSignedQPilotCertificate_q_le_hull (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (K : I.SourceSignedQPilotCarrier v R n) :
    (I.sourceSignedQPilotCertificate v R n K).qSigned <=
      (I.sourceSignedQPilotCertificate v R n K).hull.hullVolume :=
  (I.sourceSignedQPilotCertificate v R n K).q_le_hull

/-- **Signed headline composition at the actual q-pilot.**  The non-collapsed
carrier feeds the existing FiniteCertificateBridge; qSigned is the source q-pilot
signed log, and the q <= -|log Theta| comparison is the carrier's proved
comparison.  The IPL/SHE/APT evidence remains supplied, exactly as in the
existing bridge. -/
theorem sourceSignedQPilotCor312Conclusion (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (K : I.SourceSignedQPilotCarrier v R n)
    (ipl she apt : Prop) (hipl : ipl) (hshe : she) (hapt : apt) :
    Cor312Conclusion
      ((I.sourceSignedHullCertificate v R n (I.sourceQPilotSignedLog v R)
          (I.sourceSignedQPilotCarrier_comparison v R n K)
          (I.sourceSignedQPilotCarrier_qPilot_neg v R n K)).toContract
        (I.sourceSignedHullLinkEvidence v R n (I.sourceQPilotSignedLog v R)
          (I.sourceSignedQPilotCarrier_comparison v R n K)
          (I.sourceSignedQPilotCarrier_qPilot_neg v R n K)
          ipl she apt hipl hshe hapt)) :=
  cor312OfSourceSignedHullComparison I v R n (I.sourceQPilotSignedLog v R)
    (I.sourceSignedQPilotCarrier_comparison v R n K)
    (I.sourceSignedQPilotCarrier_qPilot_neg v R n K)
    ipl she apt hipl hshe hapt

/-! ## 6. The unconditional collapse at the value realization -/

/-- **The value-realized source hull has zero real log-volume, unconditionally.**
The source hull is a submonoid of the value carrier and the log-degree is
additive.  If it contained a point of positive log-degree, its powers would make
the hull log-degree unbounded and the hull volume top
(sourceHullVolume_eq_top_of_exists_pos_logDegree); otherwise every hull
log-degree is nonpositive and the hull volume is zero
(sourceHullVolume_eq_zero_of_hull_logDegree_nonpos).  In both phases the real
part is zero.  No degree-faithfulness premise is used. -/
theorem sourceRealHullVolume_eq_zero (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) :
    I.sourceRealHullVolume v R n = 0 := by
  unfold sourceRealHullVolume
  by_cases hpos : ∃ x ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)),
      0 < I.sourceLocalLogDegree v x
  · rw [(I.sourceHullVolume_eq_top_iff_exists_pos_logDegree v R n).mpr hpos,
      ENNReal.toReal_top]
  · have hnonpos : ∀ z ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)),
        I.sourceLocalLogDegree v z <= 0 := by
      intro z hz
      by_contra hz'
      exact hpos ⟨z, hz, not_le.mp hz'⟩
    rw [I.sourceHullVolume_eq_zero_of_hull_logDegree_nonpos v R n hnonpos,
      ENNReal.toReal_zero]

/-- The signed hull log-volume is unconditionally zero: the signed wrapper is
collapsed at the value realization, independently of degree faithfulness. -/
theorem sourceSignedHullLogVolume_eq_zero (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) :
    I.sourceSignedHullLogVolume v R n = 0 := by
  unfold sourceSignedHullLogVolume
  rw [I.sourceRealHullVolume_eq_zero v R n, neg_zero]

/-- **The literal (xi-f) comparison is unconditionally true at the value layer.**
With the signed hull carrier collapsed to zero, the comparison is qPilot <= 0,
which holds for every source q.  Hence the literal signed comparison has zero
discriminating power at this realization; it is not the corpus comparison. -/
theorem sourceXifSignedComparisonAtQPilot_unconditional (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    I.SourceXifSignedComparisonAtQPilot v R n := by
  unfold SourceXifSignedComparisonAtQPilot
  rw [I.sourceSignedHullLogVolume_eq_zero v R n]
  exact I.sourceQPilotSignedLog_nonpos v R

/-- **The non-collapsed carrier is empty unconditionally** at the value
realization: its positivity field contradicts the unconditional vanishing of
the real hull log-volume.  The finite non-collapsed hull cannot exist at this
level; only an ambient O-module/IQ carrier can carry it. -/
theorem not_nonempty_sourceSignedQPilotCarrier (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    ¬ Nonempty (I.SourceSignedQPilotCarrier v R n) := by
  rintro ⟨K⟩
  have hpos := K.hull_realVolume_pos
  rw [I.sourceRealHullVolume_eq_zero v R n] at hpos
  exact lt_irrefl 0 hpos

/-- **The q-scale hull bound is equivalent to the collapsed zero phase**, not to
a positive finite bound: at the value realization the only finite hull volume is
0.  Hence the numeric q-scale bound itself cannot carry a non-collapsed
comparison; the ambient carrier is unavoidable. -/
theorem sourceQPilotHullBound_iff_hullVolume_eq_zero (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    I.SourceQPilotHullBound v R n ↔ I.sourceHullVolume v R n = 0 := by
  constructor
  · intro B
    have hb : I.sourceHullVolume v R n <=
        ENNReal.ofReal (I.sourceQPilotLogMagnitude v R) :=
      (I.sourceQPilotHullBound_iff v R n).mp B
    have hfin : I.sourceHullVolume v R n < ⊤ :=
      lt_of_le_of_lt hb ENNReal.ofReal_lt_top
    exact I.sourceHullVolume_eq_zero_of_hull_logDegree_nonpos v R n
      ((I.sourceHullVolume_lt_top_iff_forall_logDegree_nonpos v R n).mp hfin)
  · intro h0
    exact (I.sourceQPilotHullBound_iff v R n).mpr (by rw [h0]; exact zero_le)

end OriginalInput
end Theorem311Source

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for the actual signed q-pilot carrier and the (xi-f)
comparison (deep-audit group C, first missing object of Card-HULLREAL).  The
q-pilot value is the actual source theta-packet quantity -|log q|, not a
parameter.  Proved: the exact signed comparison reductions; the unconditional
collapse of the value-realized signed hull (sourceRealHullVolume = 0 always), so
the literal (xi-f) comparison is unconditionally true and has zero
discriminating power at the value layer; emptiness of the non-collapsed carrier
for every realization; equivalence of the q-scale hull bound with the collapsed
zero phase; the scaled-region/O-module sufficient condition and its tight-point
necessity; and the conditional consumer wiring.  The exact missing object is an
ambient IQ/O-module carrier where the hull is not the least value-monoid
submonoid.  NOT proved: that ambient carrier, the compactness of 1,circ U, or a
non-value-realized positive finite hull.  No arbitrary qSigned, sorry, axiom,
placeholder, or True. -/
def cardHullRealSignedQPilotActual : Obligation :=
  { id := "IUT-III.corollary-3.12-card-hullreal-signed-qpilot-actual"
    source :=
      "IUT III, Corollary 3.12 proof, Steps (xi-d)-(xi-f) (III:10843-10898); " ++
        "deep-audit group C, Card-HULLREAL missing object 4"
    status := VerificationStatus.interface
    note :=
      "Actual q-pilot signed log -|log q| fixed by the source theta packet " ++
        "(sourceQPilotSignedLog; = -|logDegree of the realized q-parameter| by " ++
        "degree_of_q). Unconditional signed reduction: SourceXifSignedComparisonAtQPilot " ++
        "iff sourceRealHullVolume <= |log q|; under hfin iff sourceHullVolume <= " ++
        "ofReal |log q|. Unconditional collapse: the source hull is a submonoid " ++
        "and the log-degree additive, so a positive-degree hull point makes the " ++
        "hull volume top and otherwise all hull degrees are nonpositive and the " ++
        "volume is zero; in both phases sourceRealHullVolume = 0 " ++
        "(sourceRealHullVolume_eq_zero). Hence sourceSignedHullLogVolume = 0 and " ++
        "the literal (xi-f) comparison is unconditionally true for every source q " ++
        "(sourceXifSignedComparisonAtQPilot_unconditional), with zero discriminating " ++
        "power at the value layer. The non-collapsed carrier SourceSignedQPilotCarrier " ++
        "(q < 1 + 0 < real hull volume + q-scale bound) is empty for every " ++
        "realization (not_nonempty_sourceSignedQPilotCarrier); SourceQPilotHullBound " ++
        "is equivalent to sourceHullVolume = 0, not to a positive finite bound " ++
        "(sourceQPilotHullBound_iff_hullVolume_eq_zero). The exact missing object is " ++
        "therefore an ambient IQ/O-module carrier in which the holomorphic hull is " ++
        "not the least value-monoid submonoid; the candidate interface and the " ++
        "conditional consumer wiring (sourceSignedQPilotCertificate, " ++
        "sourceSignedQPilotCor312Conclusion) record what that carrier must supply. " ++
        "Value-level O-module route: SourceOneCircUCompactness / " ++
        "SourceUnitRegionHaarData give the containment hull subset lam . O and a " ++
        "free bound C; the q-scale bound holds whenever ld(lam) + C <= |log q|, and " ++
        "at a tight hull point this normalization is also necessary. NOT proved: " ++
        "the ambient carrier, that numeric normalization for a constructed " ++
        "O-module, positivity of a value-level hull volume (impossible here), the " ++
        "compactness of 1,circ U, or a non-value-realized realization."
    dependsOn :=
      [ "IUT-III.corollary-3.12-card-hullreal-signed-log-volume"
      , "IUT-III.corollary-3.12-card-hullreal-omodule-compactness"
      , "IUT-III.corollary-3.12-card-hullreal-contracted-source"
      , "IUT-III.source-procession-stepXI-xif-inclusion" ] }

#print axioms LeanFormal.IUT.Theorem311Source.OriginalInput.sourceQPilotSignedLog_eq_neg_abs_logDegree
#print axioms LeanFormal.IUT.Theorem311Source.OriginalInput.sourceXifSignedComparisonAtQPilot_iff_realPart_le
#print axioms LeanFormal.IUT.Theorem311Source.OriginalInput.sourceXifSignedComparisonAtQPilot_iff_hullVolume_le
#print axioms LeanFormal.IUT.Theorem311Source.OriginalInput.sourceXifSignedComparisonAtQPilot_degenerate_of_degreeFaithful
#print axioms LeanFormal.IUT.Theorem311Source.OriginalInput.sourceQPilotHullBound_iff
#print axioms LeanFormal.IUT.Theorem311Source.OriginalInput.sourceQPilotHullBound_iff_comparison_and_finite
#print axioms LeanFormal.IUT.Theorem311Source.OriginalInput.nonempty_sourceSignedQPilotCarrier_iff_comparison_and_positivity
#print axioms LeanFormal.IUT.Theorem311Source.OriginalInput.not_nonempty_sourceSignedQPilotCarrier_of_degreeFaithful
#print axioms LeanFormal.IUT.Theorem311Source.OriginalInput.not_nonempty_sourceSignedQPilotCarrier_of_contractedGenerators
#print axioms LeanFormal.IUT.Theorem311Source.OriginalInput.sourceLocalLogDegree_pow_mul
#print axioms LeanFormal.IUT.Theorem311Source.OriginalInput.sourceScaling_logDegree_nonpos_of_qPilotHullBound
#print axioms LeanFormal.IUT.Theorem311Source.OriginalInput.sourceQPilotHullBound_of_scaledRegion
#print axioms LeanFormal.IUT.Theorem311Source.OriginalInput.sourceRealHullVolume_eq_zero
#print axioms LeanFormal.IUT.Theorem311Source.OriginalInput.sourceSignedHullLogVolume_eq_zero
#print axioms LeanFormal.IUT.Theorem311Source.OriginalInput.sourceXifSignedComparisonAtQPilot_unconditional
#print axioms LeanFormal.IUT.Theorem311Source.OriginalInput.not_nonempty_sourceSignedQPilotCarrier
#print axioms LeanFormal.IUT.Theorem311Source.OriginalInput.sourceQPilotHullBound_iff_hullVolume_eq_zero
#print axioms LeanFormal.IUT.Theorem311Source.OriginalInput.sourceSignedQPilotCor312Conclusion

end LeanFormal.IUT.Audit
