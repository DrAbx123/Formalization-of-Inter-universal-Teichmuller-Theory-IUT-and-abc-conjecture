import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealEdgeNormalizationDichotomy
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceContractedSupplyRealization
import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# Card-HULLREAL R9 body: generator nonpositivity and the guarded decomposition carrier

Task `hunit-epsilon-transfer-20261016`, R9 body continuation round (report section
20).  The section 19 round proved the sharp value-layer characterization
`hull <= image` iff every generator has nonpositive log-degree
(`sourceHullVolume_le_imageVolume_iff_generators_nonpos`,
`CardHullRealEdgeNormalizationDichotomy.lean:390`), leaving the sign control of
the generators and the instantiation of the multiplicative decomposition
interface open.  This file attacks both.

* Generator sign determination.  The source links make all theaters share one
  theta packet: `linkAt_q` and `linkAt_scale`
  (`SourceOriginalInput.lean:129-137`) identify `q` and every special value
  across the whole `n`-procession.  Hence the realized log-degree of the
  theta-pilot image at any procession `n` and label `j` is, unconditionally
  (no degree-faithfulness premise), the cardinality times
  `(gaussExponent j).toNat * log(q_0)` with `q_0` the q-parameter of the
  theater at `(0,0)`
  (`sourceLocalLogDegree_thetaPilotPoint_gauss`).  Consequences:
  - every image is a contraction iff `q_0 <= 1`
    (`sourceImageLogDegree_nonpos_iff_q_le_one`; the label `j = 1` detects the
    failure because `lStar l >= 2` for `l >= 5`);
  - `q_0 <= 1` together with the scaling contraction hypothesis `hScaling`
    proves R9 (`sourceHullVolume_le_imageVolume_of_q_le_one_and_scaling`);
  - `1 < q_0` refutes R9 outright
    (`not_sourceHullVolume_le_imageVolume_of_one_lt_q`), a value-layer
    counterexample family with the label `j = 1` as witness;
  - therefore R9 iff `q_0 <= 1` and `hScaling`
    (`sourceHullVolume_le_imageVolume_iff_q_le_one_and_scaling`).

* Guarded decomposition carrier.  The section 19 interface
  `LogVolumeScaleDecomposition` quantifies its decomposition law over all sets,
  including the empty set, which forces `logScale` to vanish identically
  (`logScale_eq_zero`, proved here as the correction).  The guarded interface
  `LogVolumeScaleDecompositionNonempty` restricts the law to nonempty regions
  and records the nonemptiness of the unit region; its derived laws
  (unit-region translate, unit, multiplicativity) are re-proved under the
  guard.  The interface is instantiated on the real value-layer object
  `sourceNonpositiveLogDegreeSubmonoid v` (the global value points of
  nonpositive log-degree, `SourceContractedSupplyRealization.lean:167`) with
  regions mapped to the supremum of their log-degrees and `logScale` the
  log-degree itself, the value-layer form of [AbsTopIII] Proposition 5.7, (i),
  (b) on the contraction regime.Corpus anchors (verified against the text corpus directory):

* IUT III, Corollary 3.12 proof, Step (xi): lines 10354-10360 (`|log(q)| > 0`,
  normalization `-|log(Theta)| < 0`); 10381-10414 (possible images, holomorphic
  hulls, compactness of the `1,circ U_{j,vQ}`, `-|log(Theta)|` finite hence
  negative); 10843-10863 (log-volume of `1,circ U` read through the log-Kummer
  correspondence in the 1-column and the tensor packets of log-shells);
  10895-10899 (`-|log(q)| <= -|log(Theta)|`).
* IUT III, Remark 3.9.5, (i) (lines 7652-7680): the holomorphic hull as the
  smallest subset of the form `lambda . O` with every component of `lambda`
  nonzero.
* [AbsTopIII], Proposition 5.7, (i), (a), (b) (corpus lines 7915-7941):
  normalization `mu_k(O_k) = 1`, translation invariance, and the decomposition
  `mu^log_k(x . A) = mu^log_k(A) + dot-mu^log_k(x)`.

Honesty boundary.  R9 body remains unproved: the result here is the sharp
reduction of its value-layer content to `q_0 <= 1` plus the named scaling
hypothesis `hScaling`, together with the counterexample family in the
complementary regime `q_0 > 1`.  The decomposition instance lives on the
value-layer nonpositive-degree submonoid, not on the paper's `1,circ U`
carrier; no degree-faithfulness premise is used or needed, and the value-layer
counterexample does not assert anything about the paper's geometric carrier.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT

noncomputable section

universe u v ua uv upi umon ui

/-! ## 1. The degeneracy of the unguarded decomposition (section 19 correction) -/

namespace LogVolumeScaleDecomposition

variable {X : Type u} [Monoid X] (D : LogVolumeScaleDecomposition X)

/-- **Section 19 correction.**  The unguarded decomposition law is quantified
over every set of the carrier, including the empty set.  Testing it at `A = empty`
gives `logVolume empty = logVolume empty + logScale x`, so the multiplicative
factor of the section 19 interface is forced to vanish identically: the
interface cannot carry a nonzero `dot-mu^log`.  The guarded interface
`LogVolumeScaleDecompositionNonempty` below repairs exactly this defect. -/
theorem logScale_eq_zero (x : X) : D.logScale x = 0 := by
  have h := D.decomposition x (∅ : Set X)
  rw [Set.image_empty] at h
  linarith

end LogVolumeScaleDecomposition
/-! ## 2. The guarded decomposition interface and its laws -/

/-- The guarded form of the log-volume decomposition law of [AbsTopIII]
Proposition 5.7, (i), (b): a right multiplicative action on sets
(`A |-> A . x`), an additive log-volume split with factor `logScale`,
normalization `logVolume unitRegion = 0`, and nonemptiness of the unit region.
The decomposition law is quantified over nonempty regions only, which is the
minimal guard excluding the empty-set degeneracy of the unguarded interface. -/
structure LogVolumeScaleDecompositionNonempty (X : Type u) [Monoid X] where
  /-- The log-volume functional on regions, in log coordinates (`mu^log`). -/
  logVolume : Set X → Real
  /-- The distinguished unit region `O` of the normalization. -/
  unitRegion : Set X
  /-- The unit region is nonempty; without this the empty-set degeneracy of the
  unguarded interface reappears. -/
  unitRegion_nonempty : unitRegion.Nonempty
  /-- Normalization: `mu(O) = 1` in multiplicative coordinates, i.e.
  `mu^log(O) = 0`. -/
  normalization : logVolume unitRegion = 0
  /-- The additive `dot-mu^log` factor of the action. -/
  logScale : X → Real
  /-- The decomposition law `mu^log(A . x) = mu^log(A) + dot-mu^log(x)`,
  guarded to nonempty regions. -/
  decomposition : forall (x : X) (A : Set X), A.Nonempty ->
    logVolume ((fun a => a * x) '' A) = logVolume A + logScale x

namespace LogVolumeScaleDecompositionNonempty

variable {X : Type u} [Monoid X] (D : LogVolumeScaleDecompositionNonempty X)

/-- `dot-mu^log(x) = mu^log(x . O)`: the factor is the log-volume of the
`x`-translate of the unit region (Proposition 5.7, (i), (b), first clause). -/
theorem logScale_eq_logVolume_shift_unitRegion (x : X) :
    D.logVolume ((fun a => a * x) '' D.unitRegion) = D.logScale x := by
  have h := D.decomposition x D.unitRegion D.unitRegion_nonempty
  rw [D.normalization] at h
  exact h.trans (zero_add (D.logScale x))

/-- `dot-mu^log(1) = 0`. -/
theorem logScale_one : D.logScale 1 = 0 := by
  have hO : (fun a => a * 1) '' D.unitRegion = D.unitRegion := by
    ext b
    constructor
    · rintro ⟨a, ha, rfl⟩
      simpa using ha
    · intro hb
      exact ⟨b, hb, mul_one b⟩
  have h := D.decomposition 1 D.unitRegion D.unitRegion_nonempty
  rw [hO] at h
  linarith

/-- Additivity of `dot-mu^log` under the monoid multiplication: the factor is
an additive homomorphism into `(Real, +)` (Proposition 5.7, (i), (b), second
clause, in log coordinates). -/
theorem logScale_mul (x y : X) :
    D.logScale (x * y) = D.logScale x + D.logScale y := by
  have hcomp : (fun a => a * (x * y)) '' D.unitRegion =
      (fun b => b * y) '' ((fun a => a * x) '' D.unitRegion) := by
    rw [Set.image_image]
    simp only [mul_assoc]
  have hnonempty : ((fun a => a * x) '' D.unitRegion).Nonempty := by
    obtain ⟨o, ho⟩ := D.unitRegion_nonempty
    exact ⟨o * x, o, ho, rfl⟩
  have h1 := D.decomposition (x * y) D.unitRegion D.unitRegion_nonempty
  rw [hcomp, D.decomposition y ((fun a => a * x) '' D.unitRegion) hnonempty,
    D.decomposition x D.unitRegion D.unitRegion_nonempty] at h1
  linarith

end LogVolumeScaleDecompositionNonempty
/-! ## 3. Real-supremum and multiplicative value-group helpers -/

/-- Translation law for suprema of nonempty bounded-above sets of reals:
`sSup ((. + c) '' S) = sSup S + c`.  This is the order-theoretic content of
the decomposition law used to instantiate the guarded interface at the
log-degree carrier. -/
theorem real_sSup_image_add_const {S : Set Real} (hne : S.Nonempty)
    (hbdd : BddAbove S) (c : Real) :
    sSup ((fun y => y + c) '' S) = sSup S + c := by
  have hne' : ((fun y => y + c) '' S).Nonempty := by
    obtain ⟨s, hs⟩ := hne
    exact ⟨s + c, s, hs, rfl⟩
  have hbdd' : BddAbove ((fun y => y + c) '' S) := by
    obtain ⟨B, hB⟩ := hbdd
    exact ⟨B + c, by
      rintro y ⟨s, hs, rfl⟩
      linarith [hB hs]⟩
  refine le_antisymm ?_ ?_
  · refine csSup_le hne' ?_
    rintro y ⟨s, hs, rfl⟩
    linarith [le_csSup hbdd hs]
  · have h : sSup S <= sSup ((fun y => y + c) '' S) - c := by
      refine csSup_le hne ?_
      intro s hs
      have h1 : s + c <= sSup ((fun y => y + c) '' S) :=
        le_csSup hbdd' ⟨s, hs, rfl⟩
      linarith
    linarith

/-- Powers of `ofAdd` of a multiplied logarithm: for any real `x` and natural
`k`, the multiplicative group element `ofAdd (k * log x)` is the `k`-th power
of `ofAdd (log x)`.  This converts the Gaussian theta-pilot special values
`q^(j^2)` into powers of the standard value `ofAdd (log q)`. -/
theorem ofAdd_nat_mul_log_eq_pow (x : Real) (k : Nat) :
    Multiplicative.ofAdd ((k : Real) * Real.log x) =
      (Multiplicative.ofAdd (Real.log x)) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hcast : ((Nat.succ k : Nat) : Real) * Real.log x =
          (k : Real) * Real.log x + Real.log x := by
        push_cast
        ring
      rw [hcast, ofAdd_add, ih, pow_succ]

/-- The Gaussian exponent of the label `1` is `1`: used to detect a `q > 1`
packet through the label `j = 1`. -/
theorem gaussExponent_one_toNat : (gaussExponent (1 : Int)).toNat = 1 := by
  norm_num [gaussExponent]

/-- For `l >= 5` the label bound satisfies `lStar l >= 2`, so `1` and `-1` are
signed labels and the label `j = 1` is available as a nonvanishing witness. -/
theorem PrimeGeFive.lStar_ge_two (l : PrimeGeFive) : 2 <= lStar l.value := by
  have h := two_mul_lStar_add_one l.value l.odd
  have h5 := l.ge_five
  omega
/-! ## 4. Generator sign determination at the source value layer -/

namespace Theorem311Source
namespace OriginalInput

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- The signed label `j = 1`; available because `lStar l >= 2` for `l >= 5`. -/
def oneSignedLabel : SignedLabel l.value :=
  ⟨1, by
    have hstar : 2 <= lStar l.value := PrimeGeFive.lStar_ge_two l
    exact ⟨by omega, by omega⟩⟩

theorem oneSignedLabel_val : (oneSignedLabel (l := l)).1 = 1 :=
  rfl

theorem oneSignedLabel_ne_zero : (oneSignedLabel (l := l)).1 ≠ 0 := by
  rw [oneSignedLabel_val]
  exact one_ne_zero

/-- **The link contract at the value layer.**  At every procession `n` the
logarithm of the theta special value at `(n,0)` and label `j` is the Gaussian
exponent times `log` of the standard `q`-parameter `(I.theaterAt 0 0).thetaPacket.q`:
the links `linkAt_scale` and `linkAt_q` identify all theaters of the family
with the base theater at `(0,0)`. -/
theorem log_thetaValueAt_eq_gauss (n : ThetaPilotCarrier l)
    (j : SignedLabel l.value) :
    Real.log (I.thetaValueAt (n.val : Int) 0 j) =
      (gaussExponent j.1).toNat *
        Real.log ((I.theaterAt 0 0).thetaPacket.q) := by
  unfold thetaValueAt
  rw [I.linkAt_scale (n.val : Int) 0 0 0 j]
  exact (I.theaterAt 0 0).thetaPacket.log_scale j

/-- The theta-pilot image value is the `posRealAction` of `ofAdd` of the
Gaussian exponent times the standard `q`-log: the value-group unfolding of the
link contract. -/
theorem thetaImageValue_eq_ofAdd_gauss (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) (j : SignedLabel l.value) :
    I.thetaImageValue R n j =
      R.posRealAction (Multiplicative.ofAdd
        (((gaussExponent j.1).toNat : Real) *
          Real.log ((I.theaterAt 0 0).thetaPacket.q))) := by
  rw [I.thetaImageValue_eq R n j, log_thetaValueAt_eq_gauss (I := I) n j]

/-- Log-degree of powers: `mu_log(x ^ k) = k * mu_log(x)`. -/
theorem logDegreeAt_pow (n m : Int) (v : V) (x : I.ValueMonoidAt n m v)
    (k : Nat) :
    I.logDegreeAt n m v (x ^ k) = (k : Real) * I.logDegreeAt n m v x := by
  induction k with
  | zero => simp [I.logDegreeAt_one]
  | succ k ih =>
      rw [pow_succ, I.logDegreeAt_mul, ih]
      push_cast
      ring
/-- The log-degree of the realized `k`-th power of the standard `q`-value is
`k * log q`: the `degree_of_q` faithfulness of the source realization composed
with additivity of the log-degree on powers. -/
theorem logDegreeAt_q_pow (v : V) (R : I.SourceImageRealization v) (k : Nat) :
    I.logDegreeAt 0 0 v
        (R.posRealAction (Multiplicative.ofAdd
          ((k : Real) * Real.log ((I.theaterAt 0 0).thetaPacket.q)))) =
      (k : Real) * Real.log ((I.theaterAt 0 0).thetaPacket.q) := by
  have hpow : R.posRealAction (Multiplicative.ofAdd
        ((k : Real) * Real.log ((I.theaterAt 0 0).thetaPacket.q))) =
      (R.posRealAction (Multiplicative.ofAdd
        (Real.log ((I.theaterAt 0 0).thetaPacket.q)))) ^ k := by
    rw [ofAdd_nat_mul_log_eq_pow, map_pow]
  rw [hpow, I.logDegreeAt_pow 0 0 v, R.degree_of_q]

/-- **Unconditional generator degree formula.**  The realized log-degree of the
theta-pilot image at procession `n` and label `j` is the cardinality of the
index times `(gaussExponent j).toNat * log(q_0)`, with `q_0` the standard
`q`-parameter.  Uses only the link contract and `degree_of_q`; no
degree-faithfulness premise is involved. -/
theorem sourceLocalLogDegree_thetaPilotPoint_gauss (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (j : SignedLabel l.value) :
    I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j) =
      (Fintype.card (SourceVolumeIndex l) : Real) *
        (((gaussExponent j.1).toNat : Real) *
          Real.log ((I.theaterAt 0 0).thetaPacket.q)) := by
  unfold sourceLocalLogDegree
  simp only [I.sourceThetaPilotPoint_apply]
  have hsum : (∑ x : SourceVolumeIndex l,
      I.logDegreeAt 0 0 v (I.thetaImageValue R n j)) =
    ∑ _x : SourceVolumeIndex l,
      (((gaussExponent j.1).toNat : Real) *
        Real.log ((I.theaterAt 0 0).thetaPacket.q)) :=
    Finset.sum_congr rfl (fun i _ => by
      rw [I.thetaImageValue_eq_ofAdd_gauss v R n j]
      exact logDegreeAt_q_pow (I := I) v R ((gaussExponent j.1).toNat))
  rw [hsum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- If the standard `q`-parameter is at most `1`, every theta-pilot image has
nonpositive log-degree: the image-side half of the R9 generator condition. -/
theorem sourceImageLogDegree_nonpos_of_q_le_one (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hq : (I.theaterAt 0 0).thetaPacket.q <= 1) :
    forall j : SignedLabel l.value,
      I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j) <= 0 := by
  intro j
  rw [I.sourceLocalLogDegree_thetaPilotPoint_gauss v R n j]
  have hlogq : Real.log ((I.theaterAt 0 0).thetaPacket.q) <= 0 :=
    (Real.log_nonpos_iff (I.theaterAt 0 0).thetaPacket.q_pos.le).mpr hq
  exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _)
    (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hlogq)

/-- If the standard `q`-parameter exceeds `1`, every nonzero theta-pilot image
has strictly positive log-degree: the value-layer counterexample generator. -/
theorem sourceImageLogDegree_pos_of_one_lt_q_of_ne_zero (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (j : SignedLabel l.value) (hj : j.1 ≠ 0)
    (hq : 1 < (I.theaterAt 0 0).thetaPacket.q) :
    0 < I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j) := by
  rw [I.sourceLocalLogDegree_thetaPilotPoint_gauss v R n j]
  have hlogq : 0 < Real.log ((I.theaterAt 0 0).thetaPacket.q) :=
    Real.log_pos hq
  have hkpos : 0 < ((gaussExponent j.1).toNat : Real) := by
    have hpos : 0 < gaussExponent j.1 := by
      unfold gaussExponent
      exact sq_pos_of_ne_zero hj
    have hnat : 0 < (gaussExponent j.1).toNat := by
      have hcast : ((gaussExponent j.1).toNat : Int) = gaussExponent j.1 :=
        Int.toNat_of_nonneg (le_of_lt hpos)
      omega
    exact_mod_cast hnat
  exact mul_pos (by exact_mod_cast sourceVolumeIndex_card_pos l)
    (mul_pos hkpos hlogq)
/-- **Image-side sign dichotomy.**  Every theta-pilot image has nonpositive
log-degree iff the standard `q`-parameter is at most `1`.  The label `j = 1`
detects the failure: at `q > 1` its Gaussian exponent is `1` and its degree is
the positive number `card * log q`. -/
theorem sourceImageLogDegree_nonpos_iff_q_le_one (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    (forall j : SignedLabel l.value,
        I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j) <= 0) ↔
      (I.theaterAt 0 0).thetaPacket.q <= 1 := by
  constructor
  · intro himg
    have h1 := himg (oneSignedLabel (l := l))
    rw [I.sourceLocalLogDegree_thetaPilotPoint_gauss v R n
        (oneSignedLabel (l := l)),
      oneSignedLabel_val, gaussExponent_one_toNat, Nat.cast_one, one_mul] at h1
    have hcard : (0 : Real) < (Fintype.card (SourceVolumeIndex l) : Real) := by
      exact_mod_cast sourceVolumeIndex_card_pos l
    have hlog : Real.log ((I.theaterAt 0 0).thetaPacket.q) <= 0 :=
      nonpos_of_mul_nonpos_right h1 hcard
    exact (Real.log_nonpos_iff (I.theaterAt 0 0).thetaPacket.q_pos.le).mp hlog
  · intro hq
    exact sourceImageLogDegree_nonpos_of_q_le_one I v R n hq

/-- **Conditional R9.**  If the standard `q`-parameter is at most `1` and every
hull scaling unit has nonpositive log-degree (`hScaling`), then the R9
inequality `hull <= image` holds: the image half is discharged by the sign
dichotomy, the scaling half is the named hypothesis. -/
theorem sourceHullVolume_le_imageVolume_of_q_le_one_and_scaling (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hq : (I.theaterAt 0 0).thetaPacket.q <= 1)
    (hScaling : ∀ s ∈ I.sourceScalingUnits v,
      I.sourceLocalLogDegree v s <= 0) :
    I.sourceHullVolume v R n <= I.sourceImageVolume v R n :=
  I.sourceHullVolume_le_imageVolume_of_generator_nonpos v R n
    (sourceImageLogDegree_nonpos_of_q_le_one I v R n hq) hScaling

/-- **Unconditional counterexample family.**  If the standard `q`-parameter
exceeds `1`, then R9 fails: the label-`1` image has strictly positive
log-degree, and the powers of that hull point have unbounded log-degree while
the edge volume is finite.  No degree-faithfulness premise is involved. -/
theorem not_sourceHullVolume_le_imageVolume_of_one_lt_q (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hq : 1 < (I.theaterAt 0 0).thetaPacket.q) :
    ¬ I.sourceHullVolume v R n <= I.sourceImageVolume v R n :=
  I.not_sourceHullVolume_le_imageVolume_of_hull_logDegree_pos v R n
    ⟨I.sourceThetaPilotPoint v R n (oneSignedLabel (l := l)),
      I.sourceThetaPilotPoint_mem_sourceHolomorphicHull v R n
        (oneSignedLabel (l := l)),
      sourceImageLogDegree_pos_of_one_lt_q_of_ne_zero I v R n
        (oneSignedLabel (l := l)) oneSignedLabel_ne_zero hq⟩

/-- **Sharp value-layer determination of R9.**  The R9 inequality holds iff
the standard `q`-parameter is at most `1` and every hull scaling unit is a
contraction.  This is the sharpened form of the section 19 generator
characterization: the sign control of the theta-pilot generators is exactly
the condition `q_0 <= 1`, while the scaling half remains the named hypothesis
`hScaling`. -/
theorem sourceHullVolume_le_imageVolume_iff_q_le_one_and_scaling (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    I.sourceHullVolume v R n <= I.sourceImageVolume v R n ↔
      (I.theaterAt 0 0).thetaPacket.q <= 1 ∧
        (∀ s ∈ I.sourceScalingUnits v,
          I.sourceLocalLogDegree v s <= 0) := by
  rw [I.sourceHullVolume_le_imageVolume_iff_generators_nonpos v R n]
  exact ⟨fun h => ⟨(sourceImageLogDegree_nonpos_iff_q_le_one I v R n).mp h.1,
      h.2⟩,
    fun h => ⟨sourceImageLogDegree_nonpos_of_q_le_one I v R n h.1, h.2⟩⟩
/-! ## 5. Instantiation of the guarded interface on the log-degree carrier -/

/-- **Value-layer instantiation of the guarded decomposition.**  On the
submonoid of global value points of nonpositive log-degree
(`sourceNonpositiveLogDegreeSubmonoid v`), regions are measured by the
supremum of their log-degrees and the multiplicative factor is the log-degree
itself.  The decomposition law
`logVolume (A . x) = logVolume A + logScale x` is the translation law for
suprema of bounded-above degree sets; the unit region `{1}` is normalized by
`sourceLocalLogDegree_one`.  This is the value-layer form of [AbsTopIII]
Proposition 5.7, (i), (b) on the contraction regime; the carrier is the value
submonoid, not the paper's `1,circ U`. -/
def sourceNonpositiveLogVolumeScaleDecomposition (v : V) :
    LogVolumeScaleDecompositionNonempty
      (↥(I.sourceNonpositiveLogDegreeSubmonoid v)) where
  logVolume := fun A =>
    sSup (I.sourceLocalLogDegree v '' ((↑) '' A))
  unitRegion := {1}
  unitRegion_nonempty := Set.singleton_nonempty 1
  normalization := by
    show sSup (I.sourceLocalLogDegree v ''
      ((↑) '' ({1} : Set (↥(I.sourceNonpositiveLogDegreeSubmonoid v))))) = 0
    rw [Set.image_singleton, Set.image_singleton, Submonoid.coe_one,
      I.sourceLocalLogDegree_one, csSup_singleton]
  logScale := fun x => I.sourceLocalLogDegree v (↑x)
  decomposition := by
    intro x A hA
    have hne : (I.sourceLocalLogDegree v '' ((↑) '' A)).Nonempty := by
      obtain ⟨a, ha⟩ := hA
      exact ⟨I.sourceLocalLogDegree v (↑a), ↑a, ⟨a, ha, rfl⟩, rfl⟩
    have hbdd : BddAbove (I.sourceLocalLogDegree v '' ((↑) '' A)) := by
      refine ⟨0, ?_⟩
      rintro y ⟨b, ⟨a, ha, rfl⟩, rfl⟩
      exact a.2
    have himg : I.sourceLocalLogDegree v ''
          ((↑) '' ((fun a => a * x) '' A)) =
        (fun y : Real => y + I.sourceLocalLogDegree v (↑x)) ''
          (I.sourceLocalLogDegree v '' ((↑) '' A)) := by
      ext y
      constructor
      · rintro ⟨b, hb, rfl⟩
        obtain ⟨a, ha, rfl⟩ := hb
        obtain ⟨a', ha', rfl⟩ := ha
        refine ⟨I.sourceLocalLogDegree v (↑a'),
          ⟨↑a', ⟨a', ha', rfl⟩, rfl⟩, ?_⟩
        rw [Submonoid.coe_mul, I.sourceLocalLogDegree_mul]
      · rintro ⟨s, hs, hs_eq⟩
        obtain ⟨b, hb, rfl⟩ := hs
        obtain ⟨a, ha, rfl⟩ := hb
        refine ⟨↑(a * x), ⟨a * x, ⟨a, ha, rfl⟩, rfl⟩, ?_⟩
        rw [Submonoid.coe_mul, I.sourceLocalLogDegree_mul]
        exact hs_eq
    change sSup (I.sourceLocalLogDegree v ''
        ((↑) '' ((fun a => a * x) '' A))) =
      sSup (I.sourceLocalLogDegree v '' ((↑) '' A)) +
        I.sourceLocalLogDegree v (↑x)
    rw [himg]
    exact real_sSup_image_add_const hne hbdd (I.sourceLocalLogDegree v (↑x))

/-- The multiplicative factor of the log-degree instantiation is the
log-degree itself. -/
theorem sourceNonpositiveLogVolumeScaleDecomposition_logScale_eq (v : V)
    (x : ↥(I.sourceNonpositiveLogDegreeSubmonoid v)) :
    (I.sourceNonpositiveLogVolumeScaleDecomposition v).logScale x =
      I.sourceLocalLogDegree v (↑x) :=
  rfl

/-- The multiplicative factor of the log-degree instantiation is nonpositive
on the whole carrier: every point of the nonpositive-degree submonoid is a
contraction. -/
theorem sourceNonpositiveLogVolumeScaleDecomposition_logScale_nonpos (v : V)
    (x : ↥(I.sourceNonpositiveLogDegreeSubmonoid v)) :
    (I.sourceNonpositiveLogVolumeScaleDecomposition v).logScale x <= 0 :=
  x.2

end OriginalInput
end Theorem311Source

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for the R9 body round: the unconditional generator degree
formula from the link contract, the image-side sign dichotomy, the conditional
R9 with the named scaling hypothesis, the value-layer counterexample family for
`q > 1`, the sharp iff `R9` iff `q <= 1` plus scaling contraction, the
section 19 degeneracy correction, and the guarded decomposition interface
instantiated on the log-degree submonoid. -/
def cardHullRealGeneratorNonpositivity : Obligation :=
  { id := "IUT-III.corollary-3.12-card-hullreal-generator-nonpositivity"
    source :=
      "IUT III, Corollary 3.12 proof, Step (xi) (corpus lines 10354-10360, " ++
        "10381-10414, 10843-10863, 10895-10899); Remark 3.9.5, (i) " ++
        "(lines 7652-7680); [AbsTopIII] Proposition 5.7, (i), (a), (b) " ++
        "(corpus lines 7915-7941)"
    status := VerificationStatus.interface
    note :=
      "R9 body round. (1) Unconditional generator degree formula from the " ++
        "link contract (linkAt_q/linkAt_scale): the realized log-degree of " ++
        "the theta-pilot image at (n,0), label j, is card * " ++
        "(gaussExponent j).toNat * log(q_0); no degree-faithfulness premise. " ++
        "Hence: all images contract iff q_0 <= 1 (label j = 1 detects the " ++
        "failure); q_0 <= 1 plus scaling contraction proves R9; 1 < q_0 " ++
        "refutes R9 unconditionally (counterexample family); R9 iff q_0 <= 1 " ++
        "and hScaling. (2) Section 19 correction: the unguarded " ++
        "LogVolumeScaleDecomposition forces logScale == 0 (empty-set " ++
        "degeneracy); the guarded LogVolumeScaleDecompositionNonempty restricts " ++
        "the law to nonempty regions and is instantiated at the value layer on " ++
        "sourceNonpositiveLogDegreeSubmonoid v with logVolume = sup of " ++
        "log-degrees, logScale = log-degree, unitRegion = {1}. Value-layer " ++
        "form of [AbsTopIII] Proposition 5.7, (i), (b). NOT proved: R9 body; " ++
        "hScaling; instantiation on the paper's 1,circ U carrier (the " ++
        "multiplicative log-volume on the true carrier remains open, report " ++
        "section 20). The counterexample is a value-layer phenomenon (q_0 > 1) " ++
        "and does not assert anything about the geometric carrier."
    dependsOn :=
      [ "IUT-III.corollary-3.12-card-hullreal-edge-normalization-dichotomy",
        "IUT-III.corollary-3.12-card-hullreal-edge-normalization-reduction",
        "IUT-III.corollary-3.12-card-hullreal-contracted-source" ] }

end LeanFormal.IUT.Audit
