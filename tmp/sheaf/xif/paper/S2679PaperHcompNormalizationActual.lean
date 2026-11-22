import tmp.sheaf.xif.paper.S1527OOrderEqualityActual
import tmp.sheaf.xif.paper.S2675BadCardNoGoActual
import tmp.sheaf.xif.paper.BaseQLogVolumeActual
import tmp.sheaf.xif.paper.PaperQPilotObjectConcreteActual
import tmp.sheaf.xif.paper.PaperSignedHullSignedActual
import tmp.sheaf.xif.paper.ProcessionThetaPacketAverageActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceTheaterCarrier

/-!
# hcomp normalization audit for the card-one paper input

This file is an analysis/no-go file. It does not try to prove the old
card(V_bad) >= 5 lower-bound route; that route is refuted because the S1280
paper input has card = 1.

## Actual source data

For the S1280/S1895 paper input:

* the bad family is the singleton {S1280Place l}, card = 1;
* the unique bad q is q_b = (1/5)^order_C3, where order_C3 is the DVR order
  of the chosen completion q candidate S1487Cand;
* sourceBadQAbsLog = order_C3 * log 5;
* the bad-q absolute-log divisor is the single Finsupp
  fun₀ | paperBad0 => order_C3 * log 5, supported at the unique bad place.

## Native base-q comparison

The native base-q global magnitude is the local term baseQTotalLogMagnitude T.
Under the exact bad-q alignment (a bijection of bad index sets with pointwise
equality of the local absolute logs), it equals sourceBadQAbsLog. At the paper
S1280 selection it also equals order_C3 * log 5. So there is no missing
discrepancy constant between sourceBadQAbsLog and the native base-q magnitude:
they are the same q-side normalization.

The orphan-olean modules GlobalQPilotObjectActual and
S2681HcompBadQAlignmentActual declare the same terms but are in the
tmp.sheaf.xif.paper.PaperQPilotObject camp, which conflicts with the real
tmp.sheaf.xif.PaperQPilotObject camp used by the actual paper objects. The two
definitions are reproduced here verbatim (same terms, no new assumptions).

## hcomp normalization

hcomp is the comparison P.procession.average <= -O.qPilotLogVolume. For the
actual paper q-pilot object S1895PaperO this is exactly
P.procession.average <= sourceBadQAbsLog I.initial. For the actual source
theater Gaussian average (any C3 whose theta packet is sourceTheater l) the
average is log 5 * coeff, where

  coeff = gaussianExponentSum l / card(SignedLabel l.value).

Therefore hcomp is exactly the order inequality coeff <= order_C3. Moreover
coeff > 1 for every prime l >= 5, so hcomp forces order_C3 >= 2. In particular
the uniformizer case order_C3 = 1 refutes hcomp. The explicit legitimate
singleton source datum with q = 1/5 has sourceBadQAbsLog = log 5 and gives an
unconditional counterexample to the raw comparison for any hull with the
Gaussian average. (That datum is an actual SourceDefinition31Data over the
concrete Gaussian arithmetic; its non-scalar clause carriers are the
S1487SourceData model, irrelevant to the scalar comparison, and it is not
claimed to be the S1280 paper input.)

## Corrected statement

After dividing the theta average by coeff, the comparison becomes
log 5 <= order_C3 * log 5, which holds unconditionally from order_C3 > 0.
Equivalently, the raw hcomp must be replaced by the D4 order bound
coeff <= order_C3. This is the precise missing normalization/order condition.

No sorry, axiom, True placeholder, or native_decide is used. PUnit occurs only
as the explicit singleton bad index of the q = 1/5 counterexample, not as a
placeholder for a missing object.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2679PaperHcompNormalizationActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.PaperQPilotConcreteActual
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.ThetaPacketQIdentificationActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual
open LeanFormal.IUT.XiFPaper.S1527OOrderEqualityActual
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.XiFPaper.S2675BadCardNoGoActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.ProcessionThetaPacketAverageActual
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceTheaterCarrier

local instance s2679GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance s2679FivePrime : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

universe uX uLabel

abbrev paperBad0 (D : S1895PaperInput) : (S1895PaperInput.I D).initial.badPlaces :=
  S1527Bad0 D.l

theorem paperInput_qParameter (D : S1895PaperInput)
    (b : (S1895PaperInput.I D).initial.badPlaces) :
    (S1895PaperInput.I D).initial.reduction.qParameter b =
      ((5 : Real)⁻¹) ^ S1527OrderC3 := by
  change (S1280ReductionClause D.l).qParameter b = ((5 : Real)⁻¹) ^ S1527OrderC3
  exact S1527_qParameter_eq D.l b

theorem paperInput_abs_log_qParameter (D : S1895PaperInput)
    (b : (S1895PaperInput.I D).initial.badPlaces) :
    |Real.log ((S1895PaperInput.I D).initial.reduction.qParameter b)| =
      (S1527OrderC3 : Real) * Real.log 5 := by
  change |Real.log ((S1280ReductionClause D.l).qParameter b)| =
    (S1527OrderC3 : Real) * Real.log 5
  exact S1527_abs_log_qParameter D.l b

theorem paperInput_sourceBadQAbsLog (D : S1895PaperInput) :
    sourceBadQAbsLog (S1895PaperInput.I D).initial =
      (S1527OrderC3 : Real) * Real.log 5 := by
  rw [show (S1895PaperInput.I D).initial =
      S1527SourceData D.l D.R D.redCompat D.hredCompat D.torCompat
        D.htorCompat D.orbCompat D.horbCompat D.secCompat D.hsecCompat
        D.cusCompat D.hcusCompat from rfl]
  exact S1527_sourceBadQAbsLog D.l D.R D.redCompat D.hredCompat D.torCompat
    D.htorCompat D.orbCompat D.horbCompat D.secCompat D.hsecCompat
    D.cusCompat D.hcusCompat

theorem paperInput_bad_card (D : S1895PaperInput) :
    Nat.card (S1895PaperInput.I D).initial.badPlaces = 1 :=
  S2675_paperInput_bad_card D

theorem paperInput_bad_subsingleton (D : S1895PaperInput) :
    Subsingleton (S1895PaperInput.I D).initial.badPlaces :=
  S1280Bad_subsingleton D.l

noncomputable def badQAbsLogDivisor
    {l : PrimeGeFive} {V : Type} (I : OriginalInput l V) :
    I.initial.badPlaces →₀ Real := by
  letI := I.initial.bad_finite
  exact ∑ b : I.initial.badPlaces,
    Finsupp.single b |Real.log (I.initial.reduction.qParameter b)|

noncomputable def paperBadQAbsLogDivisor (D : S1895PaperInput) :
    (S1895PaperInput.I D).initial.badPlaces →₀ Real :=
  badQAbsLogDivisor (S1895PaperInput.I D)

theorem paperBadQAbsLogDivisor_eq_single (D : S1895PaperInput) :
    paperBadQAbsLogDivisor D =
      Finsupp.single (paperBad0 D) ((S1527OrderC3 : Real) * Real.log 5) := by
  classical
  unfold paperBadQAbsLogDivisor badQAbsLogDivisor
  letI := (S1895PaperInput.I D).initial.bad_finite
  haveI : Subsingleton (Bad (S1280Selection D.l)) := S1280Bad_subsingleton D.l
  change (∑ b : Bad (S1280Selection D.l),
      Finsupp.single b
        |Real.log ((S1280ReductionClause D.l).qParameter b)|) =
    Finsupp.single (S1527Bad0 D.l) ((S1527OrderC3 : Real) * Real.log 5)
  rw [Finset.sum_eq_single (S1527Bad0 D.l)]
  · rw [S1527_abs_log_qParameter]
  · intro b _ hb
    exact absurd (Subsingleton.elim b (S1527Bad0 D.l)) hb
  · intro h
    exact absurd (Finset.mem_univ (S1527Bad0 D.l)) h

theorem paperBadQAbsLogDivisor_value_ne_zero :
    ((S1527OrderC3 : Real) * Real.log 5) ≠ 0 := by
  have horder : (0 : Real) < (S1527OrderC3 : Real) := by
    exact_mod_cast S1487Cand.order_pos
  have hlog : (0 : Real) < Real.log 5 := Real.log_pos (by norm_num)
  exact ne_of_gt (mul_pos horder hlog)

theorem paperBadQAbsLogDivisor_support (D : S1895PaperInput) :
    (paperBadQAbsLogDivisor D).support = {paperBad0 D} := by
  rw [paperBadQAbsLogDivisor_eq_single]
  exact Finsupp.support_single_ne_zero _ paperBadQAbsLogDivisor_value_ne_zero

theorem paperBadQAbsLogDivisor_support_card (D : S1895PaperInput) :
    (paperBadQAbsLogDivisor D).support.card = 1 := by
  rw [paperBadQAbsLogDivisor_support]
  simp

noncomputable def nativeBaseQGlobalMagnitude
    {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] : Real :=
  baseQTotalLogMagnitude T

def BadQAbsLogAlignment
    {l : PrimeGeFive} {V : Type} (I : OriginalInput l V)
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] : Prop :=
  ∃ e : I.initial.badPlaces ≃ Bad (nativePlaceSelection T),
    ∀ b : I.initial.badPlaces,
      |Real.log (I.initial.reduction.qParameter b)| = baseQLogMagnitude T (e b)

theorem sourceBadQAbsLog_eq_nativeBaseQGlobalMagnitude
    {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    (h : BadQAbsLogAlignment I T) :
    sourceBadQAbsLog I.initial = nativeBaseQGlobalMagnitude T := by
  letI := I.initial.bad_finite
  obtain ⟨e, he⟩ := h
  unfold sourceBadQAbsLog nativeBaseQGlobalMagnitude baseQTotalLogMagnitude
  calc
    (∑ b : I.initial.badPlaces,
        |Real.log (I.initial.reduction.qParameter b)|) =
        ∑ b : I.initial.badPlaces, baseQLogMagnitude T (e b) := by
      refine Finset.sum_congr rfl ?_
      intro b _
      exact he b
    _ = ∑ b : Bad (nativePlaceSelection T), baseQLogMagnitude T b := by
      exact Fintype.sum_equiv e (fun b => baseQLogMagnitude T (e b))
        (fun b => baseQLogMagnitude T b) (fun b => rfl)

noncomputable def paperNativeBaseQGlobalMagnitude (l : PrimeGeFive) : Real :=
  ∑ b : Bad (S1280Selection l),
    localLogMagnitude (badPlaceQCandidate (S1280Selection l) b)

theorem paperNativeBaseQGlobalMagnitude_eq (l : PrimeGeFive) :
    paperNativeBaseQGlobalMagnitude l = (S1527OrderC3 : Real) * Real.log 5 := by
  classical
  haveI : Subsingleton (Bad (S1280Selection l)) := S1280Bad_subsingleton l
  unfold paperNativeBaseQGlobalMagnitude
  rw [Fintype.sum_eq_single (S1527Bad0 l)]
  · rw [localLogMagnitude_eq_order_mul_log]
    have hres : residueNormBase
        (sectionFiniteLift (S1280Selection l) (S1527Bad0 l).1) = 5 := by
      rw [S1527_sectionFiniteLift_eq l (S1527Bad0 l)]
      exact S1487_residueNormBase_five
    rw [hres, S1527_badPlaceQCandidate_order_eq, S1527OrderC3_eq]
  · intro x hx
    exact absurd (Subsingleton.elim x (S1527Bad0 l)) hx

theorem paperInput_sourceBadQAbsLog_eq_paperNativeBaseQGlobalMagnitude
    (D : S1895PaperInput) :
    sourceBadQAbsLog (S1895PaperInput.I D).initial =
      paperNativeBaseQGlobalMagnitude D.l := by
  rw [paperInput_sourceBadQAbsLog, paperNativeBaseQGlobalMagnitude_eq]

theorem nativeBaseQGlobalMagnitude_eq_of_paper_alignment
    (D : S1895PaperInput) (T : SourceNativeInitialThetaData.{0} D.l)
    [Fintype (Bad (nativePlaceSelection T))]
    (h : BadQAbsLogAlignment (S1895PaperInput.I D) T) :
    nativeBaseQGlobalMagnitude T = (S1527OrderC3 : Real) * Real.log 5 := by
  rw [← sourceBadQAbsLog_eq_nativeBaseQGlobalMagnitude T h]
  exact paperInput_sourceBadQAbsLog D

/-! ## 3. hcomp: the paper q-pilot object and the raw comparison -/

def paperSourceComparison
    {l : PrimeGeFive} {V : Type} {Label : Type} {Choice : Type}
    [AddGroup Label] [Preorder Choice]
    {I : OriginalInput l V} {G : Type} [Group G] [TopologicalSpace G]
    {envStrip : FPrimeStrip V} {X : Type} {label : Type} [Fintype label]
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label) : Prop :=
  P.procession.average ≤ -O.qPilotLogVolume

theorem neg_s1895PaperO_qPilotLogVolume (D : S1895PaperInput) :
    -(S1895PaperO D).qPilotLogVolume =
      sourceBadQAbsLog (S1895PaperInput.I D).initial := by
  rw [show (S1895PaperO D).qPilotLogVolume =
      sourceQPilotSignedLog (S1895PaperInput.I D).initial from rfl]
  unfold sourceQPilotSignedLog
  ring

theorem paperSourceComparison_s1895PaperO_iff
    (D : S1895PaperInput) {X : Type} {label : Type} [Fintype label]
    (P : PaperSignedHull X label) :
    paperSourceComparison (S1895PaperO D) P ↔
      P.procession.average ≤ sourceBadQAbsLog (S1895PaperInput.I D).initial := by
  unfold paperSourceComparison
  rw [neg_s1895PaperO_qPilotLogVolume]

noncomputable def gaussianExponentSum (l : PrimeGeFive) : Nat :=
  ∑ j : SignedLabel l.value, (gaussExponent j.1).toNat

noncomputable def gaussianCoefficient (l : PrimeGeFive) : Real :=
  (gaussianExponentSum l : Real) /
    (Fintype.card (SignedLabel l.value) : Real)

theorem paperSourceComparison_iff_coefficient_le_order
    (D : S1895PaperInput) {X : Type} {label : Type} [Fintype label]
    (P : PaperSignedHull X label)
    (hP : P.procession.average =
      Real.log 5 * gaussianCoefficient D.l) :
    paperSourceComparison (S1895PaperO D) P ↔
      gaussianCoefficient D.l ≤ (S1527OrderC3 : Real) := by
  rw [paperSourceComparison_s1895PaperO_iff, hP, paperInput_sourceBadQAbsLog]
  have hlog : (0 : Real) < Real.log 5 := Real.log_pos (by norm_num)
  constructor
  · intro h
    have h' : Real.log 5 * gaussianCoefficient D.l ≤
        Real.log 5 * (S1527OrderC3 : Real) := by simpa [mul_comm] using h
    exact le_of_mul_le_mul_left h' hlog
  · intro h
    calc
      Real.log 5 * gaussianCoefficient D.l ≤
          Real.log 5 * (S1527OrderC3 : Real) :=
        mul_le_mul_of_nonneg_left h hlog.le
      _ = (S1527OrderC3 : Real) * Real.log 5 := by ring

theorem sourceTheater_packet_logVolume_formula (l : PrimeGeFive) :
    (sourceTheater l).thetaPacket.logVolume =
      ∑ j : SignedLabel l.value,
        (gaussExponent j.1).toNat * (-Real.log (5 : Real)) := by
  rw [FiniteThetaPacket.logVolume_eq_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [FiniteThetaPacket.log_scale, sourceTheater_theta_q_log]

theorem actualSourceTheaterC3_signedAverage_eq
    {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (hC3 : C3.thetaPacket = (sourceTheater l).thetaPacket) :
    (c3ThetaSignedProcession C3).average =
      Real.log 5 * gaussianCoefficient l := by
  rw [c3ThetaSignedProcession_average_eq_neg, c3ThetaProcession_average, hC3,
    sourceTheater_packet_logVolume_formula]
  unfold gaussianCoefficient gaussianExponentSum
  have hcard : (c3ThetaCard (l := l) : Real) =
      (Fintype.card (SignedLabel l.value) : Real) := rfl
  rw [hcard]
  have hsum : (∑ j : SignedLabel l.value,
      ((gaussExponent j.1).toNat : Real) * (-Real.log 5)) =
      (-Real.log 5) * ((∑ j : SignedLabel l.value,
        (gaussExponent j.1).toNat : Nat) : Real) := by
    rw [Nat.cast_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum]
  ring

theorem paperSourceComparison_iff_coefficient_le_order_of_C3
    (D : S1895PaperInput) {X : Type} {label : Type} [Fintype label]
    (C3 : SourcePilotRegionData (l := D.l) (V := FinitePrimePlace 2 7)
      (S1895PaperInput.I D))
    (hC3 : C3.thetaPacket = (sourceTheater D.l).thetaPacket)
    (P : PaperSignedHull X label)
    (hP : P.procession.average = (c3ThetaSignedProcession C3).average) :
    paperSourceComparison (S1895PaperO D) P ↔
      gaussianCoefficient D.l ≤ (S1527OrderC3 : Real) := by
  rw [paperSourceComparison_iff_coefficient_le_order D P]
  rw [hP, actualSourceTheaterC3_signedAverage_eq C3 hC3]

theorem paperSourceComparison_forces_coefficient_le_order
    (D : S1895PaperInput) {X : Type} {label : Type} [Fintype label]
    (P : PaperSignedHull X label)
    (hP : P.procession.average =
      Real.log 5 * gaussianCoefficient D.l)
    (h : paperSourceComparison (S1895PaperO D) P) :
    gaussianCoefficient D.l ≤ (S1527OrderC3 : Real) :=
  (paperSourceComparison_iff_coefficient_le_order D P hP).mp h

/-! ## 4. The Gaussian coefficient is strictly larger than one -/

def extremeLabel (l : PrimeGeFive) : SignedLabel l.value :=
  ⟨(lStar l.value : Int), by
    constructor
    · have hk : (0 : Int) ≤ (lStar l.value : Int) := by exact_mod_cast Nat.zero_le _
      omega
    · exact le_rfl⟩

def negExtremeLabel (l : PrimeGeFive) : SignedLabel l.value :=
  ⟨-(lStar l.value : Int), by
    constructor
    · exact le_rfl
    · have hk : (0 : Int) ≤ (lStar l.value : Int) := by exact_mod_cast Nat.zero_le _
      omega⟩

theorem lStar_pos (l : PrimeGeFive) : 0 < lStar l.value := by
  unfold lStar
  have h5 : 5 ≤ l.value := l.ge_five
  have h4 : 4 ≤ l.value - 1 := by omega
  have h2 : 2 ≤ (l.value - 1) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    omega
  omega

theorem extremeLabel_ne_negExtremeLabel (l : PrimeGeFive) :
    extremeLabel l ≠ negExtremeLabel l := by
  intro h
  have hval := congrArg Subtype.val h
  have hk : 0 < (lStar l.value : Int) := by exact_mod_cast lStar_pos l
  change (lStar l.value : Int) = -(lStar l.value : Int) at hval
  omega

theorem gaussExponent_extreme_toNat (l : PrimeGeFive) :
    (gaussExponent (lStar l.value : Int)).toNat = (lStar l.value) ^ 2 := by
  unfold gaussExponent
  have h : ((lStar l.value : Int) ^ 2) = (((lStar l.value) ^ 2 : Nat) : Int) := by
    push_cast
    ring
  rw [h, Int.toNat_natCast]

theorem gaussExponent_negExtreme_toNat (l : PrimeGeFive) :
    (gaussExponent (-(lStar l.value : Int))).toNat = (lStar l.value) ^ 2 := by
  unfold gaussExponent
  have h : (-(lStar l.value : Int)) ^ 2 = (((lStar l.value) ^ 2 : Nat) : Int) := by
    push_cast
    ring
  rw [h, Int.toNat_natCast]

theorem two_extreme_le_gaussianExponentSum (l : PrimeGeFive) :
    2 * (lStar l.value) ^ 2 ≤ gaussianExponentSum l := by
  classical
  let a := extremeLabel l
  let b := negExtremeLabel l
  have hab : a ≠ b := by
    unfold a b
    exact extremeLabel_ne_negExtremeLabel l
  have hsub : ({a, b} : Finset (SignedLabel l.value)) ⊆ Finset.univ := by
    intro x _
    exact Finset.mem_univ x
  have hnonneg : ∀ x ∈ (Finset.univ : Finset (SignedLabel l.value)),
      x ∉ ({a, b} : Finset (SignedLabel l.value)) →
        0 ≤ (gaussExponent x.1).toNat := by
    intro x _ _
    exact Nat.zero_le _
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg
  rw [Finset.sum_pair hab] at hsum
  have ha : (gaussExponent a.1).toNat = (lStar l.value) ^ 2 := by
    unfold a extremeLabel
    exact gaussExponent_extreme_toNat l
  have hb : (gaussExponent b.1).toNat = (lStar l.value) ^ 2 := by
    unfold b negExtremeLabel
    exact gaussExponent_negExtreme_toNat l
  rw [ha, hb] at hsum
  unfold gaussianExponentSum
  simpa [two_mul, pow_two] using hsum

theorem card_signedLabel_eq (l : PrimeGeFive) :
    Fintype.card (SignedLabel l.value) = l.value :=
  SignedLabel.card_signedLabel l

theorem prime_lt_two_lStar_sq (l : PrimeGeFive) :
    l.value < 2 * (lStar l.value) ^ 2 := by
  obtain ⟨m, hm⟩ := l.odd
  have hm2 : 2 ≤ m := by
    have h5 : 5 ≤ l.value := l.ge_five
    omega
  have hls : lStar l.value = m := by
    unfold lStar
    omega
  rw [hls, hm]
  nlinarith

theorem one_lt_gaussianCoefficient (l : PrimeGeFive) :
    1 < gaussianCoefficient l := by
  unfold gaussianCoefficient
  have hcard_pos : 0 < Fintype.card (SignedLabel l.value) := by
    rw [card_signedLabel_eq]
    exact l.prime.pos
  have hcard_real : (0 : Real) <
      (Fintype.card (SignedLabel l.value) : Real) := by
    exact_mod_cast hcard_pos
  have hsum_ge : (2 * (lStar l.value) ^ 2 : Nat) ≤ gaussianExponentSum l :=
    two_extreme_le_gaussianExponentSum l
  have hsum_ge_real : ((2 * (lStar l.value) ^ 2 : Nat) : Real) ≤
      (gaussianExponentSum l : Real) := by
    exact_mod_cast hsum_ge
  have hcard_lt_nat : Fintype.card (SignedLabel l.value) <
      2 * (lStar l.value) ^ 2 := by
    rw [card_signedLabel_eq]
    exact prime_lt_two_lStar_sq l
  have hcard_lt : (Fintype.card (SignedLabel l.value) : Real) <
      ((2 * (lStar l.value) ^ 2 : Nat) : Real) := by
    exact_mod_cast hcard_lt_nat
  rw [lt_div_iff₀ hcard_real]
  have hlt : (Fintype.card (SignedLabel l.value) : Real) <
      (gaussianExponentSum l : Real) := lt_of_lt_of_le hcard_lt hsum_ge_real
  simpa using hlt

theorem paperSourceComparison_forces_two_le_order
    (D : S1895PaperInput) {X : Type} {label : Type} [Fintype label]
    (P : PaperSignedHull X label)
    (hP : P.procession.average =
      Real.log 5 * gaussianCoefficient D.l)
    (h : paperSourceComparison (S1895PaperO D) P) :
    2 ≤ S1527OrderC3 := by
  have hcoeff := paperSourceComparison_forces_coefficient_le_order D P hP h
  have h1 : (1 : Real) < (S1527OrderC3 : Real) :=
    lt_of_lt_of_le (one_lt_gaussianCoefficient D.l) hcoeff
  exact_mod_cast h1

theorem not_paperSourceComparison_of_order_one
    (D : S1895PaperInput) {X : Type} {label : Type} [Fintype label]
    (P : PaperSignedHull X label)
    (hP : P.procession.average =
      Real.log 5 * gaussianCoefficient D.l)
    (horder : S1527OrderC3 = 1) :
    ¬ paperSourceComparison (S1895PaperO D) P := by
  intro h
  have h2 := paperSourceComparison_forces_two_le_order D P hP h
  omega

theorem not_sourceComparison_numeric_of_order_one
    (D : S1895PaperInput) {X : Type} {label : Type} [Fintype label]
    (P : PaperSignedHull X label)
    (hP : P.procession.average =
      Real.log 5 * gaussianCoefficient D.l)
    (horder : S1527OrderC3 = 1) :
    ¬ (P.procession.average ≤
      sourceBadQAbsLog (S1895PaperInput.I D).initial) := by
  intro h
  have h' : paperSourceComparison (S1895PaperO D) P := by
    rw [paperSourceComparison_s1895PaperO_iff]
    exact h
  exact not_paperSourceComparison_of_order_one D P hP horder h'

/-! ## 5. The normalized comparison (the correction) -/

theorem gaussianAverage_div_coefficient
    (D : S1895PaperInput) {X : Type} {label : Type} [Fintype label]
    (P : PaperSignedHull X label)
    (hP : P.procession.average =
      Real.log 5 * gaussianCoefficient D.l) :
    P.procession.average / gaussianCoefficient D.l = Real.log 5 := by
  have hcoeff_ne : gaussianCoefficient D.l ≠ 0 := by
    have h1 := one_lt_gaussianCoefficient D.l
    linarith
  rw [hP]
  field_simp [hcoeff_ne]

theorem normalized_paperSourceComparison_holds
    (D : S1895PaperInput) {X : Type} {label : Type} [Fintype label]
    (P : PaperSignedHull X label)
    (hP : P.procession.average =
      Real.log 5 * gaussianCoefficient D.l) :
    P.procession.average / gaussianCoefficient D.l ≤
      sourceBadQAbsLog (S1895PaperInput.I D).initial := by
  rw [gaussianAverage_div_coefficient D P hP, paperInput_sourceBadQAbsLog]
  have horder : (1 : Real) ≤ (S1527OrderC3 : Real) := by
    exact_mod_cast Nat.succ_le_of_lt S1487Cand.order_pos
  have hlog : (0 : Real) < Real.log 5 := Real.log_pos (by norm_num)
  calc
    Real.log 5 = 1 * Real.log 5 := (one_mul _).symm
    _ ≤ (S1527OrderC3 : Real) * Real.log 5 :=
      mul_le_mul_of_nonneg_right horder hlog.le

noncomputable def paperSingletonNormalization : Real :=
  (S1527OrderC3 : Real) * Real.log 5

theorem log5_le_paperSingletonNormalization :
    Real.log 5 ≤ paperSingletonNormalization := by
  unfold paperSingletonNormalization
  have horder : (1 : Real) ≤ (S1527OrderC3 : Real) := by
    exact_mod_cast Nat.succ_le_of_lt S1487Cand.order_pos
  have hlog : (0 : Real) < Real.log 5 := Real.log_pos (by norm_num)
  calc
    Real.log 5 = 1 * Real.log 5 := (one_mul _).symm
    _ ≤ (S1527OrderC3 : Real) * Real.log 5 :=
      mul_le_mul_of_nonneg_right horder hlog.le

theorem two_log5_eq_paperNormalization_iff_order_two :
    (2 : Real) * Real.log 5 = paperSingletonNormalization ↔
      S1527OrderC3 = 2 := by
  unfold paperSingletonNormalization
  have hlog_ne : Real.log 5 ≠ 0 := by
    exact ne_of_gt (Real.log_pos (by norm_num))
  constructor
  · intro h
    have h' := congrArg (fun x : Real => x / Real.log 5) h
    field_simp [hlog_ne] at h'
    norm_num at h'
    rw [S1527OrderC3_eq]
    exact_mod_cast h'.symm
  · intro h
    rw [h]
    norm_num

/-! ### 4b. Card-one ceiling and the explicit order-one criterion -/

theorem paperInput_not_card_ge_five (D : S1895PaperInput) :
    ¬ 5 ≤ Nat.card (S1895PaperInput.I D).initial.badPlaces := by
  rw [paperInput_bad_card D]
  norm_num

theorem paperInput_sourceBadQAbsLog_ge_log5 (D : S1895PaperInput) :
    Real.log 5 ≤ sourceBadQAbsLog (S1895PaperInput.I D).initial := by
  rw [paperInput_sourceBadQAbsLog]
  have horder : (1 : Real) ≤ (S1527OrderC3 : Real) := by
    exact_mod_cast Nat.succ_le_of_lt S1487Cand.order_pos
  have hlog : (0 : Real) < Real.log 5 := Real.log_pos (by norm_num)
  calc
    Real.log 5 = 1 * Real.log 5 := (one_mul _).symm
    _ ≤ (S1527OrderC3 : Real) * Real.log 5 :=
      mul_le_mul_of_nonneg_right horder hlog.le

theorem paperInput_sourceBadQAbsLog_eq_log5_iff_order_one
    (D : S1895PaperInput) :
    sourceBadQAbsLog (S1895PaperInput.I D).initial = Real.log 5 ↔
      S1527OrderC3 = 1 := by
  rw [paperInput_sourceBadQAbsLog]
  have hlog_ne : Real.log 5 ≠ 0 := by
    exact ne_of_gt (Real.log_pos (by norm_num))
  constructor
  · intro h
    have h' := congrArg (fun x : Real => x / Real.log 5) h
    field_simp [hlog_ne] at h'
    norm_num at h'
    exact_mod_cast h'
  · intro h
    rw [h]
    norm_num

/-- Abstract no-go at the exact source value log 5: if the theta average is
coeff * log 5 with coeff > 1, the raw comparison fails. -/
theorem not_sourceComparison_of_source_eq_log5
    (D : S1895PaperInput) {X : Type} {label : Type} [Fintype label]
    (P : PaperSignedHull X label)
    (hP : P.procession.average =
      Real.log 5 * gaussianCoefficient D.l)
    (hsource : sourceBadQAbsLog (S1895PaperInput.I D).initial = Real.log 5) :
    ¬ (P.procession.average ≤
      sourceBadQAbsLog (S1895PaperInput.I D).initial) := by
  intro h
  rw [hsource] at h
  have hcoeff := one_lt_gaussianCoefficient D.l
  have hlog : (0 : Real) < Real.log 5 := Real.log_pos (by norm_num)
  have havg_gt : Real.log 5 < P.procession.average := by
    rw [hP]
    exact lt_mul_of_one_lt_right hlog hcoeff
  linarith

/-! ### 4c. Explicit singleton q = 1/5 counterexample -/

/-- The concrete singleton source datum with bad q = 1/5. -/
noncomputable def singletonInvFiveSourceData (l : PrimeGeFive) :
    SourceDefinition31Data.{0} l :=
  S1487SourceData (l := l) PUnit (fun _ => (5 : Real)⁻¹)
    (fun _ => by norm_num)
    (fun _ => by
      rw [Real.norm_of_nonneg (by norm_num : (0 : Real) ≤ (5 : Real)⁻¹)]
      norm_num)
    (fun _ => by norm_num)

/-- The actual input over the singleton q = 1/5 source datum. -/
noncomputable def singletonInvFiveInput (l : PrimeGeFive) :
    OriginalInput.{0, 0, 0, 0, 0} l S1487W :=
  S1487OriginalInput (singletonInvFiveSourceData l)

/-- The singleton source datum has sourceBadQAbsLog = log 5. -/
theorem singletonInvFive_sourceBadQAbsLog (l : PrimeGeFive) :
    sourceBadQAbsLog (singletonInvFiveSourceData l) = Real.log 5 := by
  unfold sourceBadQAbsLog singletonInvFiveSourceData
  letI := (singletonInvFiveSourceData l).bad_finite
  change (∑ b : PUnit,
      |Real.log ((singletonInvFiveSourceData l).reduction.qParameter b)|) =
    Real.log 5
  rw [Fintype.sum_unique]
  change |Real.log ((5 : Real)⁻¹)| = Real.log 5
  rw [Real.log_inv, abs_neg]
  exact abs_of_pos (Real.log_pos (by norm_num : (1 : Real) < 5))

/-- Generic no-go: a source bad-q magnitude of exactly log 5, together with a
Gaussian theta average coeff * log 5 (coeff > 1), refutes the raw comparison. -/
theorem not_paperSourceComparison_of_source_eq_log5
    {l : PrimeGeFive} {V : Type} {Label : Type} {Choice : Type}
    [AddGroup Label] [Preorder Choice]
    {I : OriginalInput l V} {G : Type} [Group G] [TopologicalSpace G]
    {envStrip : FPrimeStrip V} {X : Type} {label : Type} [Fintype label]
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label)
    (hO : O.qPilotLogVolume = sourceQPilotSignedLog I.initial)
    (hP : P.procession.average =
      Real.log 5 * gaussianCoefficient l)
    (hsource : sourceBadQAbsLog I.initial = Real.log 5) :
    ¬ paperSourceComparison O P := by
  intro h
  unfold paperSourceComparison at h
  rw [hO] at h
  unfold sourceQPilotSignedLog at h
  rw [hsource] at h
  have hcoeff := one_lt_gaussianCoefficient l
  have hlog : (0 : Real) < Real.log 5 := Real.log_pos (by norm_num)
  have havg_gt : Real.log 5 < P.procession.average := by
    rw [hP]
    exact lt_mul_of_one_lt_right hlog hcoeff
  linarith

/-- **Explicit actual counterexample.**  For the legitimate singleton source
datum with q = 1/5 (card 1, source bad-q magnitude log 5), any hull with the
actual Gaussian theta average has the raw comparison false. -/
theorem not_paperSourceComparison_singletonInvFive
    (l : PrimeGeFive) {X : Type} {label : Type} [Fintype label]
    (P : PaperSignedHull X label)
    (hP : P.procession.average =
      Real.log 5 * gaussianCoefficient l) :
    ¬ paperSourceComparison
      (paperQPilotObjectConcrete (l := l) (I := singletonInvFiveInput l)) P :=
  not_paperSourceComparison_of_source_eq_log5
    (paperQPilotObjectConcrete (l := l) (I := singletonInvFiveInput l))
    P rfl hP (singletonInvFive_sourceBadQAbsLog l)

#check paperInput_sourceBadQAbsLog
#check singletonInvFive_sourceBadQAbsLog
#check not_paperSourceComparison_singletonInvFive
#check paperInput_not_card_ge_five
#check paperInput_sourceBadQAbsLog_eq_log5_iff_order_one
#check not_sourceComparison_of_source_eq_log5
#check paperBadQAbsLogDivisor_eq_single
#check paperBadQAbsLogDivisor_support_card
#check sourceBadQAbsLog_eq_nativeBaseQGlobalMagnitude
#check paperNativeBaseQGlobalMagnitude_eq
#check paperSourceComparison_iff_coefficient_le_order
#check paperSourceComparison_forces_two_le_order
#check not_paperSourceComparison_of_order_one
#check normalized_paperSourceComparison_holds
#print axioms actualSourceTheaterC3_signedAverage_eq
#print axioms paperSourceComparison_iff_coefficient_le_order_of_C3
#print axioms paperInput_sourceBadQAbsLog
#print axioms paperNativeBaseQGlobalMagnitude_eq
#print axioms paperInput_sourceBadQAbsLog_eq_log5_iff_order_one
#print axioms singletonInvFive_sourceBadQAbsLog
#print axioms not_paperSourceComparison_singletonInvFive
#print axioms paperSourceComparison_iff_coefficient_le_order
#print axioms paperSourceComparison_forces_two_le_order
#print axioms normalized_paperSourceComparison_holds

end LeanFormal.IUT.XiFPaper.S2679PaperHcompNormalizationActual
end

