import tmp.sheaf.xif.paper.S1916HaarSignedAverageActual
import tmp.sheaf.xif.paper.S865RootHaarFactorNormPowActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.LocalFieldProductHull
import LeanFormal.IUT.IUTII.Theta.FiniteThetaPacket
import Mathlib

/-!
# S1931: the paper/source-selected arithmetic Haar and the exact first missing

S1916 proved that

  arithmeticTupleHullUnitLogVolume places tuple
    + Real.log (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal
  = (c3ThetaSignedProcession C3).average

(the S1904 reduction HaarSignedAverageProof.SignedUnitFactorThetaComparison) is
*not* a consequence of the in-tree Haar interface for an arbitrary additive Haar
measure mu: it is exactly the equation

  mu (arithmeticTupleCanonicalHull places tuple) = ofReal (exp (signed average)),

i.e. a normalization condition on mu, with a unique normalizing scalar.

This file removes that normalization freedom in the paper's way and isolates
what is then genuinely missing.

## 1. The source-selected arithmetic Haar

The paper's arithmetic Haar is normalized on the unit region (the
lambda * O normalization with lambda = 1 on the canonical unit reference).
Here it is the actual measure

  paperArithmeticHaar places tuple mu
    := (mu (arithmeticTupleCanonicalUnitReference places tuple))^{-1} * mu,

which is again an additive Haar measure and satisfies
paperArithmeticHaar unitReference = 1.  Nothing else is imposed: this is the
source normalization, not a fake one.

## 2. What the comparison becomes

At this source Haar the unit-reference logarithm vanishes, so the comparison is
*the mu-free real equation*

  arithmeticTupleHullUnitLogVolume places tuple
    = (c3ThetaSignedProcession C3).average

(SourceHaarHullThetaComparison).  In particular the target at the source Haar is
independent of the auxiliary additive Haar mu (only the actual arithmetic data
places, tuple and the source packet C3 remain).  This is exactly S1916's
"unique normalizing scalar" freedom removed in the source's direction.

Equivalently, at the source Haar the canonical-hull C6 mass is

  paperArithmeticHaar (arithmeticTupleCanonicalHull places tuple)
    = ofReal (exp (arithmeticTupleHullUnitLogVolume places tuple)),

so the remaining content is the comparison of two actual numbers.

## 3. The exact first missing

The hull side is computed as a norm-power (the C6 analogue of S865's
rootHaarFactor_normPow_actual): the hull unit log-volume is the logarithmic Haar
character Real.log (distribHaarChar ...) of the least scaling vector of the
canonical hull inside the actual field-product decomposition.  The theta side is
the Gaussian packet: with W = sum_j j^2 over the signed labels and
card = #(SignedLabel l.value),

  (c3ThetaSignedProcession C3).average = - (Real.log q * W) / card,
  q = C3.thetaPacket.q.

Therefore the exact first missing is the single real equation

  Real.log C3.thetaPacket.q
    = - (arithmeticTupleHullUnitLogVolume places tuple * card) / W

(s1931FirstMissing_logq): the source q-parameter of the theta packet is the
exponential of minus the normalized arithmetic hull index.  Consequences proved
here:

* the comparison is satisfiable by exactly one packet q (existence and
  uniqueness of the realizing packet at the fixed arithmetic data);
* it forces q <= 1 (because the hull unit log-volume is nonnegative), hence it
  fails for every packet with q > 1;
* for the trivial packet q = 1 it holds iff the C6 canonical hull and the
  canonical unit reference have the same actual Haar mass.

This is a genuine comparison of arithmetic data with theta data.  It is not a
normalization and not an arbitrary mu; the S865 norm-power law and the C6
norm-power law are recorded in sections 3 and 6, and the missing equation is the
*carrier-level* identification joining them, which no in-tree theorem supplies
(the root-extension carrier of the paper Theta values and the completion tensor
carrier of the C6 canonical hull are not identified; S342 is the carrier gap).

No sorry, admit, axiom, True, PUnit or arbitrary inhabitant is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1931SourceHaarSignedAverageActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.HaarSignedAverageProof
open LeanFormal.IUT.XiFPaper.ProcessionThetaPacketAverageActual
open LeanFormal.IUT.XiFPaper.S1916HaarSignedAverageActual
open LeanFormal.IUT.LocalFieldProductHull
open MeasureTheory
open scoped BigOperators

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {K : Type ua} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {iota : Type uv} [Fintype iota] {W : iota -> Type ui}
variable (places : (i : iota) -> W i -> FinitePlaceAtPrime K p)
variable (tuple : (i : iota) -> W i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (mu : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure mu]
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-! ## 1. The paper/source-selected arithmetic Haar -/

/-- **The source-selected arithmetic Haar measure.**  The actual additive Haar
measure on the C6 arithmetic tensor carrier normalized on the canonical unit
reference (the paper's unit-region normalization).  It is obtained from the
given additive Haar measure by the positive scalar that makes the canonical
unit reference have mass one; no property of the hull is built into it. -/
noncomputable def paperArithmeticHaar : Measure (ArithmeticTensorTupleBlock places tuple) :=
  (mu (arithmeticTupleCanonicalUnitReference places tuple))⁻¹ • mu

/-- The source Haar is again an additive Haar measure: the normalization scalar
is positive and finite because the canonical unit reference has positive finite
mass. -/
theorem paperArithmeticHaar_addHaar :
    Measure.IsAddHaarMeasure (paperArithmeticHaar places tuple mu) := by
  have h := measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple mu
  exact Measure.IsAddHaarMeasure.smul mu
    (ENNReal.inv_ne_zero.mpr h.2.2.ne)
    (ENNReal.inv_ne_top.mpr h.2.1.ne')

/-- **The defining property of the source Haar**: the canonical unit reference
has mass exactly one. -/
theorem paperArithmeticHaar_unitReference :
    paperArithmeticHaar places tuple mu
        (arithmeticTupleCanonicalUnitReference places tuple) = 1 := by
  have h := measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple mu
  unfold paperArithmeticHaar
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel h.2.1.ne' h.2.2.ne

/-- The canonical-hull logarithm at the source Haar is the unit-relative hull
log-volume itself. -/
theorem paperArithmeticHaar_hull_log :
    Real.log ((paperArithmeticHaar places tuple mu)
        (arithmeticTupleCanonicalHull places tuple)).toReal =
      arithmeticTupleHullUnitLogVolume places tuple := by
  letI : Measure.IsAddHaarMeasure (paperArithmeticHaar places tuple mu) :=
    paperArithmeticHaar_addHaar places tuple mu
  have hrel := arithmeticTupleCanonicalRegions_relativeLogVolume places tuple
    (paperArithmeticHaar places tuple mu)
  have hunit := paperArithmeticHaar_unitReference places tuple mu
  rw [hunit, ENNReal.toReal_one, Real.log_one, sub_zero] at hrel
  exact hrel

/-- **The C6 canonical-hull mass at the source Haar** is the exponential of the
actual unit-relative hull log-volume.  In particular the hull mass readout is no
longer an adjustable Haar normalization. -/
theorem paperArithmeticHaar_hull_mass :
    ((paperArithmeticHaar places tuple mu)
        (arithmeticTupleCanonicalHull places tuple)).toReal =
      Real.exp (arithmeticTupleHullUnitLogVolume places tuple) := by
  letI : Measure.IsAddHaarMeasure (paperArithmeticHaar places tuple mu) :=
    paperArithmeticHaar_addHaar places tuple mu
  have hpos : 0 < ((paperArithmeticHaar places tuple mu)
      (arithmeticTupleCanonicalHull places tuple)).toReal := by
    have h := (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple
      (paperArithmeticHaar places tuple mu)).1
    exact ENNReal.toReal_pos h.1.ne' h.2.ne
  rw [← Real.exp_log hpos, paperArithmeticHaar_hull_log places tuple mu]

/-! ## 2. The target at the source Haar is the mu-free comparison -/

/-- **The mu-free comparison.**  This is what the S1904/S1916 unit-factor
identity becomes once the Haar measure is the paper's source-selected one.  It
involves only the actual arithmetic data places, tuple and the source theta
packet C3. -/
def SourceHaarHullThetaComparison : Prop :=
  arithmeticTupleHullUnitLogVolume places tuple =
    (c3ThetaSignedProcession C3).average

/-- **The source-Haar reduction.**  At the paper/source-selected arithmetic Haar
the target identity is exactly the mu-free comparison above.  Hence every
arbitrary-mu normalization freedom of S1916 is removed by the source
unit-region normalization, and the residual content is a genuine equation. -/
theorem paperArithmeticHaar_signedUnitFactor_iff :
    SignedUnitFactorThetaComparison (l := l) (V := V) (I := I)
        (places := places) (tuple := tuple) (paperArithmeticHaar places tuple mu) C3 ↔
      SourceHaarHullThetaComparison (l := l) (V := V) (I := I)
        (places := places) (tuple := tuple) C3 := by
  unfold SignedUnitFactorThetaComparison SourceHaarHullThetaComparison
  rw [paperArithmeticHaar_unitReference places tuple mu, ENNReal.toReal_one, Real.log_one,
    add_zero]

/-- The target at the source Haar is independent of the auxiliary additive Haar
measure used to build the source Haar: the source normalization selects the same
comparison equation for every additive Haar input. -/
theorem sourceHaar_comparison_independent_of_initialHaar
    (nu : Measure (ArithmeticTensorTupleBlock places tuple)) [Measure.IsAddHaarMeasure nu] :
    SignedUnitFactorThetaComparison (l := l) (V := V) (I := I)
        (places := places) (tuple := tuple) (paperArithmeticHaar places tuple mu) C3 ↔
      SignedUnitFactorThetaComparison (l := l) (V := V) (I := I)
        (places := places) (tuple := tuple) (paperArithmeticHaar places tuple nu) C3 :=
  (paperArithmeticHaar_signedUnitFactor_iff
      (l := l) (V := V) (I := I) (places := places) (tuple := tuple) (mu := mu) C3).trans
    (paperArithmeticHaar_signedUnitFactor_iff
      (l := l) (V := V) (I := I) (places := places) (tuple := tuple) (mu := nu) C3).symm

/-- The source-Haar hull mass is the actual hull mass at the given additive Haar
measure up to the unit-reference scalar. -/
theorem paperArithmeticHaar_hull_apply :
    (paperArithmeticHaar places tuple mu) (arithmeticTupleCanonicalHull places tuple) =
      (mu (arithmeticTupleCanonicalUnitReference places tuple))⁻¹ *
        mu (arithmeticTupleCanonicalHull places tuple) := by
  unfold paperArithmeticHaar
  rw [Measure.smul_apply, smul_eq_mul]

/-- **The hull-mass equation at the source Haar.**  For every real a, the source
Haar gives the canonical hull mass ofReal (exp a) exactly when the actual
unit-relative hull log-volume is a. -/
theorem paperArithmeticHaar_hull_measure_eq_iff (a : ℝ) :
    (paperArithmeticHaar places tuple mu) (arithmeticTupleCanonicalHull places tuple) =
        ENNReal.ofReal (Real.exp a) ↔
      arithmeticTupleHullUnitLogVolume places tuple = a := by
  letI : Measure.IsAddHaarMeasure (paperArithmeticHaar places tuple mu) :=
    paperArithmeticHaar_addHaar places tuple mu
  have hpos : 0 < ((paperArithmeticHaar places tuple mu)
      (arithmeticTupleCanonicalHull places tuple)).toReal := by
    have h := (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple
      (paperArithmeticHaar places tuple mu)).1
    exact ENNReal.toReal_pos h.1.ne' h.2.ne
  have hfin : (paperArithmeticHaar places tuple mu)
      (arithmeticTupleCanonicalHull places tuple) < ⊤ :=
    (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple
      (paperArithmeticHaar places tuple mu)).1.2
  have hlog := paperArithmeticHaar_hull_log places tuple mu
  constructor
  · intro h
    have hto : ((paperArithmeticHaar places tuple mu)
        (arithmeticTupleCanonicalHull places tuple)).toReal = Real.exp a := by
      rw [h, ENNReal.toReal_ofReal (le_of_lt (Real.exp_pos a))]
    have hexp : Real.exp (arithmeticTupleHullUnitLogVolume places tuple) = Real.exp a := by
      rw [← hlog, Real.exp_log hpos]
      exact hto
    exact Real.exp_injective hexp
  · intro h
    have hto : ((paperArithmeticHaar places tuple mu)
        (arithmeticTupleCanonicalHull places tuple)).toReal = Real.exp a := by
      rw [← Real.exp_log hpos, hlog, h]
    calc (paperArithmeticHaar places tuple mu)
          (arithmeticTupleCanonicalHull places tuple)
        = ENNReal.ofReal ((paperArithmeticHaar places tuple mu)
            (arithmeticTupleCanonicalHull places tuple)).toReal :=
          (ENNReal.ofReal_toReal hfin.ne).symm
      _ = ENNReal.ofReal (Real.exp a) := by rw [hto]

/-- The exact C6 hull-mass form at the source Haar: the target is the statement
that the source Haar gives the canonical hull mass exp (signed average). -/
theorem paperArithmeticHaar_comparison_iff_hull_mass :
    SignedUnitFactorThetaComparison (l := l) (V := V) (I := I)
        (places := places) (tuple := tuple) (paperArithmeticHaar places tuple mu) C3 ↔
      (paperArithmeticHaar places tuple mu) (arithmeticTupleCanonicalHull places tuple) =
        ENNReal.ofReal (Real.exp ((c3ThetaSignedProcession C3).average)) := by
  rw [paperArithmeticHaar_signedUnitFactor_iff
    (l := l) (V := V) (I := I) (places := places) (tuple := tuple) (mu := mu) C3]
  unfold SourceHaarHullThetaComparison
  exact (paperArithmeticHaar_hull_measure_eq_iff (places := places) (tuple := tuple)
    (mu := mu) ((c3ThetaSignedProcession C3).average)).symm

/-- **The named exact first missing of S1931**: the source-Haar comparison. -/
def S1931FirstMissing : Prop :=
  SourceHaarHullThetaComparison (l := l) (V := V) (I := I)
    (places := places) (tuple := tuple) C3

/-- The target identity at the source Haar is exactly the named first missing. -/
theorem s1931_firstMissing_iff_comparison :
    S1931FirstMissing (l := l) (V := V) (I := I)
        (places := places) (tuple := tuple) C3 ↔
      SignedUnitFactorThetaComparison (l := l) (V := V) (I := I)
        (places := places) (tuple := tuple) (paperArithmeticHaar places tuple mu) C3 :=
  (paperArithmeticHaar_signedUnitFactor_iff
    (l := l) (V := V) (I := I) (places := places) (tuple := tuple) (mu := mu) C3).symm

/-! ## 3. The hull side as a norm-power (the C6 analogue of S865) -/

/-- **Norm-power computation of the actual hull unit log-volume.**  The C6
canonical hull is a least lambda * O region in the actual field-product
decomposition, hence its unit-relative log-volume is the logarithmic
distributive Haar character of the least scaling vector.  This is the C6
counterpart of S865's rootHaarFactor_normPow_actual / the root character-norm
comparison. -/
theorem arithmeticTupleHullUnitLogVolume_eq_log_distribHaarChar
    {J : Type (max ua uv)} [Finite J] {E : J -> Type (max ua uv)}
    [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
    [∀ j, FiniteDimensional ℚ_[p] (E j)] [∀ j, ProperSpace (E j)]
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) -> E j)) :
    ∃ (lam : (j : J) -> E j) (hlam : ∀ j, lam j ≠ 0),
      arithmeticTupleHullUnitLogVolume places tuple =
        Real.log (distribHaarChar ((j : J) -> E j) (scalingUnits lam hlam) : ℝ) := by
  obtain ⟨lam, hlam, hregion⟩ := exists_hull_eq_region
    (isCompact_arithmeticTupleFieldLogImage places tuple e)
    ⟨1, one_mem_arithmeticTupleFieldLogImage places tuple e⟩
    (fun _ => ⟨1, one_mem_arithmeticTupleFieldLogImage places tuple e, one_ne_zero⟩)
  refine ⟨lam, hlam, ?_⟩
  letI : MeasurableSpace ((j : J) -> E j) := borel _
  letI : BorelSpace ((j : J) -> E j) := ⟨rfl⟩
  rw [arithmeticTupleHullUnitLogVolume_eq places tuple e, hregion]
  exact normalizedLogVolume_region Measure.addHaar lam hlam

/-! ## 4. The theta side: the actual signed average is a Gaussian q-power -/

/-- The Gaussian weight sum sum_j j^2 over the signed labels of l. -/
noncomputable def sourceThetaWeightSum (l : PrimeGeFive) : ℝ :=
  ∑ j : SignedLabel l.value, ((gaussExponent j.1).toNat : ℝ)

/-- The Gaussian weight sum is strictly positive (the label 1 contributes 1). -/
theorem sourceThetaWeightSum_pos (l : PrimeGeFive) : 0 < sourceThetaWeightSum l := by
  have hstar : 2 ≤ lStar l.value := by
    have hodd := l.odd
    have h2 := two_mul_lStar_add_one l.value hodd
    have h5 := l.ge_five
    omega
  have hmem : (1 : Int) ∈ Set.Icc (-(lStar l.value : Int)) (lStar l.value : Int) := by
    constructor
    · have h2 : (2 : Int) ≤ (lStar l.value : Int) := by exact_mod_cast hstar
      omega
    · have h2 : (1 : Int) ≤ (lStar l.value : Int) := by
        have h3 : (2 : Int) ≤ (lStar l.value : Int) := by exact_mod_cast hstar
        omega
      exact h2
  have hterm : ((gaussExponent ((⟨1, hmem⟩ : SignedLabel l.value) : Int)).toNat : ℝ) = 1 := by
    norm_num [gaussExponent]
  have hle : ((gaussExponent ((⟨1, hmem⟩ : SignedLabel l.value) : Int)).toNat : ℝ) ≤
      sourceThetaWeightSum l := by
    unfold sourceThetaWeightSum
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun j : SignedLabel l.value => ((gaussExponent j.1).toNat : ℝ))
      (fun i _ => by positivity) (@Finset.mem_univ (SignedLabel l.value)
        (signedLabelFintype l.value) (⟨1, hmem⟩ : SignedLabel l.value))
  rw [hterm] at hle
  linarith

/-- The actual theta packet log-volume is the Gaussian weight sum times log q. -/
theorem thetaPacket_logVolume_eq :
    C3.thetaPacket.logVolume = sourceThetaWeightSum l * Real.log C3.thetaPacket.q := by
  have h : C3.thetaPacket.logVolume =
      ∑ j : SignedLabel l.value,
        ((gaussExponent j.1).toNat : ℝ) * Real.log C3.thetaPacket.q := by
    unfold FiniteThetaPacket.logVolume
    exact Finset.sum_congr rfl (fun j _ => FiniteThetaPacket.log_scale C3.thetaPacket j)
  rw [h, ← Finset.sum_mul]
  rfl

/-- **The actual signed procession average in terms of the packet parameter q.** -/
theorem signedAverage_eq_neg :
    (c3ThetaSignedProcession C3).average =
      - (Real.log C3.thetaPacket.q * sourceThetaWeightSum l) /
        (c3ThetaCard (l := l) : ℝ) := by
  rw [c3ThetaSignedProcession_average_eq_neg, c3ThetaProcession_average,
    thetaPacket_logVolume_eq]
  ring

/-- Elementary algebra: the two linear forms are equivalent for nonzero
denominators. -/
theorem neg_div_iff_neg_div (a b c d : ℝ) (hc : c ≠ 0) (hd : d ≠ 0) :
    a = - (b * d) / c ↔ b = - (a * c) / d := by
  rw [eq_div_iff hc, eq_div_iff hd]
  constructor <;> intro h <;> linarith

/-! ## 5. The exact first missing: the source q determined by the hull index -/

/-- **The exact first missing in its precise form.**  At the source Haar the
target identity is equivalent to the single real equation

  log q = - (hullUnitLogVolume * card) / W,

i.e. the source theta packet parameter q is determined by the actual arithmetic
canonical-hull log index.  This is not a Haar normalization: the Haar side is
fixed by the source unit-region normalization, and what remains is a comparison
of two actual numeric invariants. -/
theorem s1931FirstMissing_logq :
    S1931FirstMissing (l := l) (V := V) (I := I)
        (places := places) (tuple := tuple) C3 ↔
      Real.log C3.thetaPacket.q =
        - (arithmeticTupleHullUnitLogVolume places tuple * (c3ThetaCard (l := l) : ℝ)) /
            sourceThetaWeightSum l := by
  have hC : (0 : ℝ) < (c3ThetaCard (l := l) : ℝ) := by
    exact_mod_cast c3ThetaCard_pos (l := l)
  have hW : (0 : ℝ) < sourceThetaWeightSum l := sourceThetaWeightSum_pos l
  unfold S1931FirstMissing SourceHaarHullThetaComparison
  rw [signedAverage_eq_neg]
  exact neg_div_iff_neg_div (arithmeticTupleHullUnitLogVolume places tuple)
    (Real.log C3.thetaPacket.q) (c3ThetaCard (l := l) : ℝ) (sourceThetaWeightSum l)
    (ne_of_gt hC) (ne_of_gt hW)

/-- Replacing the source theta packet by the Gaussian packet of a packet
parameter q inside the same source data. -/
noncomputable def withThetaPacket (q : ℝ) (hq : 0 < q) :
    SourcePilotRegionData (l := l) (V := V) I :=
  { C3 with thetaPacket := FiniteThetaPacket.ofQ q hq }

/-- The replaced packet has the prescribed q. -/
theorem withThetaPacket_packet_q (q : ℝ) (hq : 0 < q) :
    (withThetaPacket (l := l) (V := V) (I := I) C3 q hq).thetaPacket.q = q := rfl

/-- The source-Haar comparison at the replaced packet is exactly the
q-determination equation. -/
theorem sourceHaar_comparison_at_packet_iff (q : ℝ) (hq : 0 < q) :
    S1931FirstMissing (l := l) (V := V) (I := I) (places := places) (tuple := tuple)
        (withThetaPacket (l := l) (V := V) (I := I) C3 q hq) ↔
      Real.log q =
        - (arithmeticTupleHullUnitLogVolume places tuple * (c3ThetaCard (l := l) : ℝ)) /
            sourceThetaWeightSum l := by
  have h := s1931FirstMissing_logq (l := l) (V := V) (I := I)
    (places := places) (tuple := tuple)
    (C3 := withThetaPacket (l := l) (V := V) (I := I) C3 q hq)
  rw [withThetaPacket_packet_q] at h
  exact h

/-- **The comparison is satisfiable by exactly one packet parameter**: the
exponential of minus the normalized hull index. -/
theorem sourceHaar_comparison_packet_exists :
    ∃ (q : ℝ) (hq : 0 < q),
      S1931FirstMissing (l := l) (V := V) (I := I) (places := places) (tuple := tuple)
        (withThetaPacket (l := l) (V := V) (I := I) C3 q hq) := by
  refine ⟨Real.exp (- (arithmeticTupleHullUnitLogVolume places tuple *
      (c3ThetaCard (l := l) : ℝ)) / sourceThetaWeightSum l), Real.exp_pos _, ?_⟩
  rw [sourceHaar_comparison_at_packet_iff]
  exact Real.log_exp _

/-- **Uniqueness**: two packet parameters realizing the source-Haar comparison
coincide. -/
theorem sourceHaar_comparison_packet_unique
    {q1 : ℝ} (hq1 : 0 < q1) {q2 : ℝ} (hq2 : 0 < q2)
    (h1 : S1931FirstMissing (l := l) (V := V) (I := I) (places := places) (tuple := tuple)
      (withThetaPacket (l := l) (V := V) (I := I) C3 q1 hq1))
    (h2 : S1931FirstMissing (l := l) (V := V) (I := I) (places := places) (tuple := tuple)
      (withThetaPacket (l := l) (V := V) (I := I) C3 q2 hq2)) :
    q1 = q2 := by
  have hlog1 := (sourceHaar_comparison_at_packet_iff (l := l) (V := V) (I := I)
    (places := places) (tuple := tuple) (C3 := C3) q1 hq1).mp h1
  have hlog2 := (sourceHaar_comparison_at_packet_iff (l := l) (V := V) (I := I)
    (places := places) (tuple := tuple) (C3 := C3) q2 hq2).mp h2
  have hexp : Real.exp (Real.log q1) = Real.exp (Real.log q2) := by rw [hlog1, hlog2]
  rwa [Real.exp_log hq1, Real.exp_log hq2] at hexp

/-- **Sign consequence**: the source-Haar comparison forces q <= 1, because the
actual unit-relative hull log-volume is nonnegative.  Hence it fails for every
packet with q > 1. -/
theorem sourceHaar_comparison_forces_q_le_one
    (h : S1931FirstMissing (l := l) (V := V) (I := I)
      (places := places) (tuple := tuple) C3) :
    C3.thetaPacket.q ≤ 1 := by
  have hlog := (s1931FirstMissing_logq (l := l) (V := V) (I := I)
    (places := places) (tuple := tuple) (C3 := C3)).mp h
  have hhull : 0 ≤ arithmeticTupleHullUnitLogVolume places tuple :=
    arithmeticTupleHullUnitLogVolume_nonneg places tuple
  have hC : (0 : ℝ) < (c3ThetaCard (l := l) : ℝ) := by
    exact_mod_cast c3ThetaCard_pos (l := l)
  have hW : (0 : ℝ) < sourceThetaWeightSum l := sourceThetaWeightSum_pos l
  have hnonpos : Real.log C3.thetaPacket.q ≤ 0 := by
    rw [hlog, neg_div]
    have hmul : 0 ≤ arithmeticTupleHullUnitLogVolume places tuple *
        (c3ThetaCard (l := l) : ℝ) := mul_nonneg hhull (le_of_lt hC)
    exact neg_nonpos.mpr (div_nonneg hmul (le_of_lt hW))
  by_contra hle
  have hle' : 1 < C3.thetaPacket.q := not_le.mp hle
  have hpos : 0 < Real.log C3.thetaPacket.q := Real.log_pos hle'
  linarith

/-- The source-Haar comparison is false for every theta packet with q > 1. -/
theorem sourceHaar_comparison_false_of_one_lt_q (hq : 1 < C3.thetaPacket.q) :
    ¬ S1931FirstMissing (l := l) (V := V) (I := I)
      (places := places) (tuple := tuple) C3 :=
  fun h => absurd (sourceHaar_comparison_forces_q_le_one
    (l := l) (V := V) (I := I) (places := places) (tuple := tuple) (C3 := C3) h)
    (not_le.mpr hq)

/-- **The trivial packet q = 1 case.**  The comparison at q = 1 holds exactly
when the unit-relative hull log-volume vanishes. -/
theorem sourceHaar_comparison_at_one_iff :
    S1931FirstMissing (l := l) (V := V) (I := I) (places := places) (tuple := tuple)
        (withThetaPacket (l := l) (V := V) (I := I) C3 1 zero_lt_one) ↔
      arithmeticTupleHullUnitLogVolume places tuple = 0 := by
  rw [sourceHaar_comparison_at_packet_iff (l := l) (V := V) (I := I)
    (places := places) (tuple := tuple) (C3 := C3) 1 zero_lt_one, Real.log_one]
  have hC : (0 : ℝ) < (c3ThetaCard (l := l) : ℝ) := by
    exact_mod_cast c3ThetaCard_pos (l := l)
  have hW : (0 : ℝ) < sourceThetaWeightSum l := sourceThetaWeightSum_pos l
  constructor
  · intro h
    have h' : - (arithmeticTupleHullUnitLogVolume places tuple *
        (c3ThetaCard (l := l) : ℝ)) / sourceThetaWeightSum l = 0 := h.symm
    rw [div_eq_zero_iff] at h'
    rcases h' with h' | h'
    · have hmul : arithmeticTupleHullUnitLogVolume places tuple *
          (c3ThetaCard (l := l) : ℝ) = 0 := by linarith
      exact (mul_eq_zero.mp hmul).resolve_right (ne_of_gt hC)
    · exact absurd h' (ne_of_gt hW)
  · intro h
    rw [h]
    simp

/-- The unit-relative hull log-volume vanishes exactly when the C6 canonical
hull and the canonical unit reference have the same actual Haar mass. -/
theorem hullUnitLogVolume_eq_zero_iff_measure_eq :
    arithmeticTupleHullUnitLogVolume places tuple = 0 ↔
      mu (arithmeticTupleCanonicalHull places tuple) =
        mu (arithmeticTupleCanonicalUnitReference places tuple) := by
  have hregions := measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple mu
  have hhullfin : mu (arithmeticTupleCanonicalHull places tuple) < ⊤ := hregions.1.2
  have hunitfin : mu (arithmeticTupleCanonicalUnitReference places tuple) < ⊤ := hregions.2.2
  have hrel := arithmeticTupleCanonicalRegions_relativeLogVolume places tuple mu
  constructor
  · intro h
    have hlog : Real.log (mu (arithmeticTupleCanonicalHull places tuple)).toReal =
        Real.log (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal := by
      linarith
    have hpos1 : 0 < (mu (arithmeticTupleCanonicalHull places tuple)).toReal :=
      ENNReal.toReal_pos hregions.1.1.ne' hhullfin.ne
    have hpos2 : 0 < (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal :=
      ENNReal.toReal_pos hregions.2.1.ne' hunitfin.ne
    have htoReal : (mu (arithmeticTupleCanonicalHull places tuple)).toReal =
        (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal :=
      Real.log_injOn_pos (Set.mem_Ioi.mpr hpos1) (Set.mem_Ioi.mpr hpos2) hlog
    calc mu (arithmeticTupleCanonicalHull places tuple)
        = ENNReal.ofReal (mu (arithmeticTupleCanonicalHull places tuple)).toReal :=
          (ENNReal.ofReal_toReal hhullfin.ne).symm
      _ = ENNReal.ofReal (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal := by
          rw [htoReal]
      _ = mu (arithmeticTupleCanonicalUnitReference places tuple) :=
          ENNReal.ofReal_toReal hunitfin.ne
  · intro h
    rw [← hrel, h, sub_self]

/-- **The trivial packet q = 1 comparison is the statement that the C6 canonical
hull has the same Haar mass as the canonical unit reference.** -/
theorem sourceHaar_comparison_at_one_iff_hull_measure_eq :
    S1931FirstMissing (l := l) (V := V) (I := I) (places := places) (tuple := tuple)
        (withThetaPacket (l := l) (V := V) (I := I) C3 1 zero_lt_one) ↔
      mu (arithmeticTupleCanonicalHull places tuple) =
        mu (arithmeticTupleCanonicalUnitReference places tuple) := by
  have h1 := sourceHaar_comparison_at_one_iff (l := l) (V := V) (I := I)
    (places := places) (tuple := tuple) (C3 := C3)
  have h2 := hullUnitLogVolume_eq_zero_iff_measure_eq (places := places) (tuple := tuple)
    (mu := mu)
  exact h1.trans h2

/-! ## 6. The constructive direction: the target from the source-q identification -/

/-- **Conditional proof of the target at the source Haar.**  The target identity
at the paper/source-selected arithmetic Haar follows from the single explicit
source-q identification

  log q = - (hull * card) / W.

This is the constructive direction of the exact first missing: no arbitrary mu
and no further normalization enters. -/
theorem signedUnitFactor_of_sourceQ
    (hq : Real.log C3.thetaPacket.q =
      - (arithmeticTupleHullUnitLogVolume places tuple * (c3ThetaCard (l := l) : ℝ)) /
          sourceThetaWeightSum l) :
    SignedUnitFactorThetaComparison (l := l) (V := V) (I := I)
      (places := places) (tuple := tuple) (paperArithmeticHaar places tuple mu) C3 :=
  (s1931_firstMissing_iff_comparison (l := l) (V := V) (I := I)
    (places := places) (tuple := tuple) (mu := mu) C3).mp
    ((s1931FirstMissing_logq (l := l) (V := V) (I := I)
      (places := places) (tuple := tuple) (C3 := C3)).mpr hq)

/-- **Conditional C6 hull-mass statement at the source Haar** from the source-q
identification: the canonical hull has mass exp of the signed average. -/
theorem paperArithmeticHaar_hull_mass_of_sourceQ
    (hq : Real.log C3.thetaPacket.q =
      - (arithmeticTupleHullUnitLogVolume places tuple * (c3ThetaCard (l := l) : ℝ)) /
          sourceThetaWeightSum l) :
    (paperArithmeticHaar places tuple mu) (arithmeticTupleCanonicalHull places tuple) =
      ENNReal.ofReal (Real.exp ((c3ThetaSignedProcession C3).average)) :=
  (paperArithmeticHaar_comparison_iff_hull_mass (l := l) (V := V) (I := I)
    (places := places) (tuple := tuple) (mu := mu) C3).mp
    (signedUnitFactor_of_sourceQ (l := l) (V := V) (I := I)
      (places := places) (tuple := tuple) (mu := mu) (C3 := C3) hq)

/-! ## 7. The S865 root norm-power input (root-carrier analogue) -/

section RootNormPowerInput

open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S861RootCharacterNormComparisonActual

variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- **S865 norm-power law, logarithmic form.**  On the root extension carrier
where the paper Theta values root_b^{j^2} live, the logarithmic distributive
Haar character of a field unit is its degree times the log norm.  This is the
root-carrier norm-power law proved by rootHaarFactor_normPow_actual (S865) via
the S861 character/norm comparison; it is the shape that the C6 hull norm-power
theorem above also has.  The two carriers are *not* identified in the tree
(rootNormedExtension T b versus the completion tensor
ArithmeticTensorTupleBlock places tuple), and that unproved identification is
exactly the carrier gap of the first missing, not a normalization question. -/
theorem rootHaarFactor_log_norm_pow (lam : (rootNormedExtension T b)ˣ) :
    Real.log (distribHaarChar (rootNormedExtension T b) lam : ℝ) =
      (Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) : ℝ) *
        Real.log ‖(lam : rootNormedExtension T b)‖ :=
  rootNormedCharacterNormComparison_of_factorNormPow
    (l := l) T b (Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b))
    (S865RootHaarFactorNormPowActual.rootHaarFactor_normPow_actual (l := l) T b) lam

end RootNormPowerInput

/-! ## 8. Summary: the exact content of the source-Haar target -/

/-- **S1931 exact content.**  At the paper/source-selected arithmetic Haar the
target identity is

* equivalent to the mu-free hull/theta comparison,
* equivalent to the canonical-hull mass being exp (hull unit log volume),
* equivalent to the determination of the source theta packet parameter q by the
  actual hull log index, with that q realizable and unique.

It is therefore a genuine arithmetic/theta identification, not a Haar
normalization, and its Haar normalization part is discharged by the source
selection. -/
theorem s1931_source_haar_exact_content :
    (SignedUnitFactorThetaComparison (l := l) (V := V) (I := I)
        (places := places) (tuple := tuple) (paperArithmeticHaar places tuple mu) C3 ↔
      S1931FirstMissing (l := l) (V := V) (I := I)
        (places := places) (tuple := tuple) C3) ∧
    ((paperArithmeticHaar places tuple mu)
        (arithmeticTupleCanonicalHull places tuple)).toReal =
      Real.exp (arithmeticTupleHullUnitLogVolume places tuple) ∧
    (S1931FirstMissing (l := l) (V := V) (I := I)
        (places := places) (tuple := tuple) C3 ↔
      Real.log C3.thetaPacket.q =
        - (arithmeticTupleHullUnitLogVolume places tuple * (c3ThetaCard (l := l) : ℝ)) /
            sourceThetaWeightSum l) ∧
    (∃ (q : ℝ) (hq : 0 < q),
      S1931FirstMissing (l := l) (V := V) (I := I) (places := places) (tuple := tuple)
        (withThetaPacket (l := l) (V := V) (I := I) C3 q hq)) ∧
    (∀ (q : ℝ) (hq : 0 < q),
      S1931FirstMissing (l := l) (V := V) (I := I) (places := places) (tuple := tuple)
        (withThetaPacket (l := l) (V := V) (I := I) C3 q hq) → q ≤ 1) :=
  ⟨paperArithmeticHaar_signedUnitFactor_iff (l := l) (V := V) (I := I)
      (places := places) (tuple := tuple) (mu := mu) C3,
    paperArithmeticHaar_hull_mass places tuple mu,
    s1931FirstMissing_logq (l := l) (V := V) (I := I)
      (places := places) (tuple := tuple) (C3 := C3),
    sourceHaar_comparison_packet_exists (l := l) (V := V) (I := I)
      (places := places) (tuple := tuple) (C3 := C3),
    fun q hq h => by
      have hlog := (sourceHaar_comparison_at_packet_iff (l := l) (V := V) (I := I)
        (places := places) (tuple := tuple) (C3 := C3) q hq).mp h
      have hhull : 0 ≤ arithmeticTupleHullUnitLogVolume places tuple :=
        arithmeticTupleHullUnitLogVolume_nonneg places tuple
      have hC : (0 : ℝ) < (c3ThetaCard (l := l) : ℝ) := by
        exact_mod_cast c3ThetaCard_pos (l := l)
      have hW : (0 : ℝ) < sourceThetaWeightSum l := sourceThetaWeightSum_pos l
      have hnonpos : Real.log q ≤ 0 := by
        rw [hlog, neg_div]
        have hmul : 0 ≤ arithmeticTupleHullUnitLogVolume places tuple *
            (c3ThetaCard (l := l) : ℝ) := mul_nonneg hhull (le_of_lt hC)
        exact neg_nonpos.mpr (div_nonneg hmul (le_of_lt hW))
      by_contra hle
      have hle' : 1 < q := not_le.mp hle
      have hpos : 0 < Real.log q := Real.log_pos hle'
      linarith⟩

/-! ## 9. Axiom probes -/

#print axioms paperArithmeticHaar_addHaar
#print axioms paperArithmeticHaar_unitReference
#print axioms paperArithmeticHaar_hull_log
#print axioms paperArithmeticHaar_hull_mass
#print axioms paperArithmeticHaar_signedUnitFactor_iff
#print axioms sourceHaar_comparison_independent_of_initialHaar
#print axioms paperArithmeticHaar_comparison_iff_hull_mass
#print axioms arithmeticTupleHullUnitLogVolume_eq_log_distribHaarChar
#print axioms sourceThetaWeightSum_pos
#print axioms thetaPacket_logVolume_eq
#print axioms signedAverage_eq_neg
#print axioms s1931FirstMissing_logq
#print axioms sourceHaar_comparison_packet_exists
#print axioms sourceHaar_comparison_packet_unique
#print axioms sourceHaar_comparison_forces_q_le_one
#print axioms sourceHaar_comparison_at_one_iff_hull_measure_eq
#print axioms signedUnitFactor_of_sourceQ
#print axioms paperArithmeticHaar_hull_mass_of_sourceQ
#print axioms rootHaarFactor_log_norm_pow
#print axioms s1931_source_haar_exact_content

end LeanFormal.IUT.XiFPaper.S1931SourceHaarSignedAverageActual

end
