import tmp.sheaf.xif.paper.S1280SourceDefinition31Actual
import tmp.sheaf.xif.paper.S2688BadReductionSelectionActual
import tmp.sheaf.xif.paper.S2681HcompMinimalInputActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange

/-!
# S2689: the actual per-place bad-q absolute log and its log 5 + log 2161 lower bound

Layer: source q-side (sourceBadQAbsLog), consumer: the hcomp bad-q data of
S2681HcompMinimalInputActual (HcompSourceBadQData).

## What is actual here

* sourceBadQAbsLog_actual S is literally the per-place sum
  sum_{b : S.badPlaces} |log (S.reduction.qParameter b)|, the same formula as
  Theorem311Source.sourceBadQAbsLog (proved equal by rfl).  No singleton
  substitution is made anywhere.
* log_residueNormBase_le_localLogMagnitude is the pointwise bound for an
  actual completion q-candidate at an actual finite place: the actual order
  formula |log ||q||| = order * log (residueNormBase place) of
  ArithmeticQPilotBaseChange.localLogMagnitude_eq_order_mul_log, together
  with order >= 1, gives log (residueNormBase place) <= |log ||q|||.
* log_residueCharacteristic_le_abs_log_badPlaceQProxy is the same per-place
  bound for the assembled source reduction clause: the actual source
  q-parameter at a bad place is p_b^{-1} ^ order_b, so its absolute log is at
  least log p_b.
* actualFivePlace_abs_log_qParameter and actualFivePlace_log_le compute the
  actual five-place source datum: the concrete Gaussian five place has
  residueNormBase = 5 and |log q_b| = order_b * log 5 >= log 5.  The bad
  index runs over the actual Bad (S1280Selection l); we never replace the sum
  by {5}.

## The conditional two-place theorem

S2689ActualBadQPlace R records one actual per-place datum: a bad index, the
arithmetic residue norm base N_b, the discrete order order_b >= 1, and the
per-place order formula |log q_b| = order_b * log N_b.  The formula is a
field, because SourceDefinition31Data itself contains no residue norm for an
abstract bad index; identifying a bad index with an actual place is the missing
data.  From two distinct such data with bases 5 and 2161 we prove

  log 5 + log 2161 <= sourceBadQAbsLog_actual S,

and hence 2 * log 5 <= sourceBadQAbsLog_actual S since log 5 < log 2161.
The same conclusion is also available from the bare pointwise hypotheses
log 5 <= |log q_{b5}| and log 2161 <= |log q_{b2161}|.

## hcomp consequence

concreteSourceComparison_of_twoPlaces combines the lower bound with
S2681HcompMinimalInputActual.concreteComparison_iff_weightSum_le_badQAbsLog:

  log 5 * (W / card) <= 2 log 5 and the two-place data imply hcomp.

The Gaussian coefficient bound is kept as an explicit hypothesis; at
l.value = 5 it is the proved identity W / card = 2
(concreteSourceComparison_of_twoPlaces_five).  hcomp is not asserted
unconditionally.

## Exact missing actual data (no fake)

* S2688HasBadPlace2161 l (an actual Fmod-place of residue characteristic
  2161 in the actual bad set S2688BadFmodSet l, i.e. with a proved
  multiplicative reduction at some F-place above it) has NO inhabitant in
  the tree.  MissingActualBadPlace2161 is a verbatim abbreviation of that
  proposition, not an assumption.
* The concrete S1280Selection has V_mod_bad = {concreteGaussianFivePlace};
  S1280Selection_no_2161_badPlace proves it contains no place of residue
  characteristic 2161, and S1280Bad_subsingleton makes two distinct bad
  indices impossible.  So the two-place theorem cannot be instantiated on the
  synthetic singleton selection; the paper's corrected V_bad = {5, 2161}
  needs a source place selection carrying the 2161 place together with its
  actual multiplicative-reduction proof and its actual q-candidate/order
  normalization.  Those are exactly the missing data reported at the end.
* No paper source in the tree identifies 2161 with an element of the paper's
  V_bad; the only occurrences of 2161 in LeanFormal are
  TateContraction.lean / Example36TateUniformization.lean, where
  10805 = 5 * 2161 and 2161 has 5-adic norm one (an unrelated arithmetic
  computation, not a bad-reduction place).  The S2161BaseChangeAPIActual
  file is a different, unrelated task (scheme-map base change API).

No sorry, admit, axiom, native_decide, True, PUnit witness, or
singleton substitution is used.
-/

noncomputable section
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2689SourceBadQAbsLogActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.ThetaPacketQIdentificationActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S2688BadReductionSelectionActual
open LeanFormal.IUT.XiFPaper.S2681HcompMinimalInputActual
open LeanFormal.IUT.XiFPaper.ConcreteThetaLinkSourceActual
open LeanFormal.IUT.XiFPaper.ProcessionThetaPacketAverageActual
open LeanFormal.IUT.XiFPaper.S1931SourceHaarSignedAverageActual
open LeanFormal.IUT.XiFPaper.S2679HcompLocalBoundsActual

universe u uX uLabel

local instance s2689GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-! ## 1. The actual per-place bad-q absolute log -/

/-- The actual source bad-q absolute log, as the per-place sum over the actual
bad place index of |log q_b|.  This repeats the formula of
Theorem311Source.sourceBadQAbsLog in this namespace; no singleton
substitution is made. -/
noncomputable def sourceBadQAbsLog_actual {l : PrimeGeFive}
    (S : SourceDefinition31Data l) : Real :=
  letI := S.bad_finite
  ∑ b : S.badPlaces, |Real.log (S.reduction.qParameter b)|

/-- The actual per-place definition is literally the existing source scalar. -/
theorem sourceBadQAbsLog_actual_eq_sourceBadQAbsLog {l : PrimeGeFive}
    (S : SourceDefinition31Data l) :
    sourceBadQAbsLog_actual S = sourceBadQAbsLog S := rfl

/-- The actual per-place sum is nonnegative. -/
theorem sourceBadQAbsLog_actual_nonneg {l : PrimeGeFive}
    (S : SourceDefinition31Data l) :
    0 ≤ sourceBadQAbsLog_actual S := by
  unfold sourceBadQAbsLog_actual
  letI := S.bad_finite
  exact Finset.sum_nonneg (fun b _ => abs_nonneg _)

/-! ## 2. Pointwise per-place lower bound log N <= |log q_b| -/

/-- Pure arithmetic form of the per-place bound: if q = N^{-1} ^ n with
N >= 2 and n >= 1, then |log q| >= log N. -/
theorem log_le_abs_log_inv_pow {N : ℝ} (hN : 2 ≤ N) (n : ℕ) (hn : 1 ≤ n) :
    Real.log N ≤ |Real.log (N⁻¹ ^ n)| := by
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [Real.log_pow, Real.log_inv]
  rw [show (n : ℝ) * -Real.log N = -((n : ℝ) * Real.log N) by ring]
  rw [abs_neg, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg n) (le_of_lt hlog))]
  nlinarith

/-- The local log magnitude of an actual completion q-candidate is the absolute
logarithm of its completion norm. -/
theorem localLogMagnitude_eq_abs_log_norm
    {K : Type u} [Field K] [NumberField K]
    {place : NumberField.FinitePlace K}
    (parameter : FinitePlaceQCandidate place) :
    localLogMagnitude parameter = |Real.log ‖parameter.q‖| := by
  unfold localLogMagnitude localSignedLog
  rw [abs_of_neg (Real.log_neg (qNorm_pos parameter) (qNorm_lt_one parameter))]

/-- Actual per-place pointwise bound for a completion q-candidate, with the
actual residue norm base N = residueNormBase place and the actual discrete
order n = parameter.order >= 1: log N <= localLogMagnitude. -/
theorem log_residueNormBase_le_localLogMagnitude
    {K : Type u} [Field K] [NumberField K]
    {place : NumberField.FinitePlace K}
    (parameter : FinitePlaceQCandidate place) :
    Real.log (residueNormBase place) ≤ localLogMagnitude parameter := by
  rw [localLogMagnitude_eq_order_mul_log parameter]
  have hlog : 0 < Real.log (residueNormBase place) := log_residueNormBase_pos place
  have horder : (1 : ℝ) ≤ (parameter.order : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt parameter.order_pos)
  nlinarith

/-- The same pointwise bound in the absolute-logarithm form
log (residueNormBase place) <= |log ||q|||. -/
theorem log_residueNormBase_le_abs_log_norm
    {K : Type u} [Field K] [NumberField K]
    {place : NumberField.FinitePlace K}
    (parameter : FinitePlaceQCandidate place) :
    Real.log (residueNormBase place) ≤ |Real.log ‖parameter.q‖| := by
  rw [← localLogMagnitude_eq_abs_log_norm parameter]
  exact log_residueNormBase_le_localLogMagnitude parameter

/-- Actual per-place pointwise bound for the assembled source reduction clause:
at a bad moduli place of residue characteristic p, the source q-parameter is
p^{-1} ^ order_b, so log p <= |log q_b|.  This is the per-place form
|log q_b| >= log N_b with N_b = p. -/
theorem log_residueCharacteristic_le_abs_log_badPlaceQProxy
    {l : PrimeGeFive} {A : InitialThetaArithmeticData.{u} l}
    (P : SourcePlaceSelection A) (b : Bad P) :
    Real.log ((NumberFieldFinitePlace.residueCharacteristic b.1 : ℕ) : ℝ) ≤
      |Real.log (badPlaceQProxy P b)| := by
  unfold badPlaceQProxy
  refine log_le_abs_log_inv_pow ?_ _ (Nat.succ_le_of_lt (badPlaceQCandidate_order_pos P b))
  have hp := NumberFieldFinitePlace.residueCharacteristic_prime b.1
  exact_mod_cast hp.two_le

/-! ## 3. The actual five place: residue norm 5 and |log q_b| >= log 5 -/

/-- The arithmetic residue norm base at the actual Gaussian five place is 5.
This repeats the residue-norm computation of S1487_residueNormBase_five from
the actual residue field cardinality
concreteGaussianFivePlaceResidueField_card. -/
theorem residueNormBase_fivePlace (l : PrimeGeFive) :
    residueNormBase (S1280Place l) = 5 := by
  show residueNormBase concreteGaussianFivePlace = 5
  unfold residueNormBase
  have hcard :
      Nat.card (NumberFieldFinitePlace.ResidueField concreteGaussianFivePlace) = 5 :=
    LeanFormal.IUT.IUTII.Frobenioid.Example36.concreteGaussianFivePlaceResidueField_card
  have habs :
      Ideal.absNorm (concreteGaussianFivePlace.maximalIdeal.asIdeal) = 5 := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    simpa [NumberFieldFinitePlace.ResidueField, NumberFieldFinitePlace.underlyingPrime]
      using hcard
  rw [habs]
  norm_num

/-- The unique actual bad moduli place of S1280Selection is the concrete
Gaussian five place. -/
theorem badPlace_eq_fivePlace (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) :
    b.1 = S1280Place l := by
  letI : Subsingleton (Bad (S1280Selection l)) := S1280Bad_subsingleton l
  have hmem : S1280Place l ∈ (S1280Selection l).V_mod_bad := by
    rw [S1280Selection_V_mod_bad]
    exact Set.mem_singleton _
  have hb : b = ⟨S1280Place l, hmem⟩ :=
    Subsingleton.elim b ⟨S1280Place l, hmem⟩
  exact congrArg Subtype.val hb

/-- The actual residue norm base at any actual bad index of S1280Selection is
5. -/
theorem badPlace_residueNormBase_eq_five (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) :
    residueNormBase b.1 = 5 := by
  rw [badPlace_eq_fivePlace l b, residueNormBase_fivePlace l]

/-- The actual source q-parameter absolute log at the concrete Gaussian five
place is the actual order times log 5. -/
theorem actualFivePlace_abs_log_qParameter (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) :
    |Real.log ((S1280ReductionClause l).qParameter b)| =
      ((badPlaceQCandidate (S1280Selection l) b).order : ℝ) * Real.log 5 := by
  rw [S1280ReductionClause_qParameter_eq]
  set n : ℕ := (badPlaceQCandidate (S1280Selection l) b).order with hn
  have hlog5 : 0 < Real.log (5 : ℝ) := Real.log_pos (by norm_num)
  rw [Real.log_pow, Real.log_inv]
  rw [show (n : ℝ) * -Real.log (5 : ℝ) =
      -((n : ℝ) * Real.log (5 : ℝ)) by ring]
  rw [abs_neg, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg n) (le_of_lt hlog5))]

/-- The actual five-place source q-parameter satisfies |log q_b| >= log 5. -/
theorem actualFivePlace_log_le (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) :
    Real.log 5 ≤ |Real.log ((S1280ReductionClause l).qParameter b)| := by
  rw [actualFivePlace_abs_log_qParameter]
  have hlog5 : 0 < Real.log (5 : ℝ) := Real.log_pos (by norm_num)
  have horder : (1 : ℝ) ≤ ((badPlaceQCandidate (S1280Selection l) b).order : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt
      (badPlaceQCandidate_order_pos (S1280Selection l) b))
  nlinarith

/-- The actual five-place q-parameter absolute log expressed through the actual
residue norm base 5. -/
theorem actualFivePlace_abs_log_eq_order_mul_residueNormBase (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) :
    |Real.log ((S1280ReductionClause l).qParameter b)| =
      ((badPlaceQCandidate (S1280Selection l) b).order : ℝ) *
        Real.log (residueNormBase b.1) := by
  rw [badPlace_residueNormBase_eq_five l b]
  exact actualFivePlace_abs_log_qParameter l b

/-! ## 4. Two actual bad places and the log 5 + log 2161 lower bound -/

/-- One actual per-place datum at a source bad index.  base is the arithmetic
residue norm N_b of the underlying actual place (5 at the concrete five
place; 2161 would be required for the second paper bad prime), order is the
positive discrete order of the source q-parameter, and abs_log_eq is the
per-place order formula |log q_b| = order_b * log N_b.  That formula is a
hypothesis: SourceDefinition31Data carries no residue norm for an abstract
bad index, so the identification with an actual place is the missing data
recorded in section 6. -/
structure S2689ActualBadQPlace {Selected Bad : Type u}
    (R : SourceReductionClause Selected Bad) where
  b : Bad
  base : ℝ
  base_ge_two : 2 ≤ base
  order : ℕ
  order_pos : 0 < order
  abs_log_eq : |Real.log (R.qParameter b)| = (order : ℝ) * Real.log base

/-- Pointwise per-place bound from one actual per-place datum. -/
theorem onePlace_log_le_of_data {Selected Bad : Type u}
    {R : SourceReductionClause Selected Bad}
    (d : S2689ActualBadQPlace R) :
    Real.log d.base ≤ |Real.log (R.qParameter d.b)| := by
  rw [d.abs_log_eq]
  have hlog : 0 < Real.log d.base := Real.log_pos (by linarith [d.base_ge_two])
  have horder : (1 : ℝ) ≤ (d.order : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt d.order_pos)
  nlinarith [hlog, horder]

/-- Two distinct summands with nonnegative values are bounded by the sum. -/
theorem two_terms_le_sum {α : Type u} [Fintype α] (f : α → ℝ)
    (hf : ∀ a, 0 ≤ f a) {a b : α} (hne : a ≠ b) :
    f a + f b ≤ ∑ x : α, f x := by
  classical
  have hsub : ({a, b} : Finset α) ⊆ Finset.univ := Finset.subset_univ _
  have h := Finset.sum_le_sum_of_subset_of_nonneg (f := f) hsub
    (fun x _ _ => hf x)
  rw [Finset.sum_pair hne] at h
  simpa using h

/-- The two-place sum bound at the level of a source reduction clause. -/
theorem twoPlace_sum_log_le {Selected Bad : Type u}
    {R : SourceReductionClause Selected Bad} [Fintype Bad]
    (d5 d2161 : S2689ActualBadQPlace R)
    (hne : d5.b ≠ d2161.b)
    (hbase5 : d5.base = 5) (hbase2161 : d2161.base = 2161) :
    Real.log 5 + Real.log 2161 ≤ ∑ b : Bad, |Real.log (R.qParameter b)| := by
  have h5 := onePlace_log_le_of_data d5
  have h2161 := onePlace_log_le_of_data d2161
  rw [hbase5] at h5
  rw [hbase2161] at h2161
  have hsum := two_terms_le_sum
    (fun b : Bad => |Real.log (R.qParameter b)|)
    (fun b => abs_nonneg _) hne
  linarith

/-- **The conditional two-place lower bound.**  If the actual source data have
two distinct bad indices carrying the two actual per-place data with residue
norm bases 5 and 2161, then log 5 + log 2161 is bounded by the actual
per-place bad-q absolute log.  No singleton substitution is used: this is the
sum over the actual bad index S.badPlaces. -/
theorem log5_add_log2161_le_sourceBadQAbsLog_actual
    {l : PrimeGeFive} (S : SourceDefinition31Data l)
    (d5 d2161 : S2689ActualBadQPlace S.reduction)
    (hne : d5.b ≠ d2161.b)
    (hbase5 : d5.base = 5) (hbase2161 : d2161.base = 2161) :
    Real.log 5 + Real.log 2161 ≤ sourceBadQAbsLog_actual S := by
  unfold sourceBadQAbsLog_actual
  letI := S.bad_finite
  exact twoPlace_sum_log_le d5 d2161 hne hbase5 hbase2161

/-- The same conditional two-place bound from the bare pointwise hypotheses
log 5 <= |log q_{b5}| and log 2161 <= |log q_{b2161}|. -/
theorem log5_add_log2161_le_sourceBadQAbsLog_actual_of_abs
    {l : PrimeGeFive} (S : SourceDefinition31Data l)
    (b5 b2161 : S.badPlaces) (hne : b5 ≠ b2161)
    (h5 : Real.log 5 ≤ |Real.log (S.reduction.qParameter b5)|)
    (h2161 : Real.log 2161 ≤ |Real.log (S.reduction.qParameter b2161)|) :
    Real.log 5 + Real.log 2161 ≤ sourceBadQAbsLog_actual S := by
  unfold sourceBadQAbsLog_actual
  letI := S.bad_finite
  have hsum := two_terms_le_sum
    (fun b : S.badPlaces => |Real.log (S.reduction.qParameter b)|)
    (fun b => abs_nonneg _) hne
  linarith

/-- **The 2 log 5 bad-q lower bound.**  Since log 5 < log 2161, the
two-place lower bound gives 2 log 5 <= sourceBadQAbsLog_actual S. -/
theorem two_mul_log5_le_sourceBadQAbsLog_actual
    {l : PrimeGeFive} (S : SourceDefinition31Data l)
    (d5 d2161 : S2689ActualBadQPlace S.reduction)
    (hne : d5.b ≠ d2161.b)
    (hbase5 : d5.base = 5) (hbase2161 : d2161.base = 2161) :
    2 * Real.log 5 ≤ sourceBadQAbsLog_actual S := by
  have h := log5_add_log2161_le_sourceBadQAbsLog_actual S d5 d2161 hne hbase5 hbase2161
  have hlt : Real.log 5 < Real.log 2161 :=
    Real.log_lt_log (by norm_num) (by norm_num)
  linarith

/-- The actual five-place datum as a S2689ActualBadQPlace for the actual
S1280ReductionClause: this is the per-place actual five data, proved (not
hypothesised). -/
def actualFivePlaceData (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) :
    S2689ActualBadQPlace (S1280ReductionClause l) where
  b := b
  base := 5
  base_ge_two := by norm_num
  order := (badPlaceQCandidate (S1280Selection l) b).order
  order_pos := badPlaceQCandidate_order_pos (S1280Selection l) b
  abs_log_eq := actualFivePlace_abs_log_qParameter l b

/-! ## 5. The hcomp bad-q side -/

/-- The source bad-q data of S2681 (2 log 5 <= sourceBadQAbsLog I.initial) from
two actual per-place data.  This is exactly the badQ field of
HcompMinimalInput, in its source-side form HcompSourceBadQData. -/
theorem hcompSourceBadQData_of_twoPlaces
    {l : PrimeGeFive}
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
    (d5 d2161 : S2689ActualBadQPlace I.initial.reduction)
    (hne : d5.b ≠ d2161.b)
    (hbase5 : d5.base = 5) (hbase2161 : d2161.base = 2161) :
    HcompSourceBadQData I := by
  unfold HcompSourceBadQData
  have h := two_mul_log5_le_sourceBadQAbsLog_actual I.initial d5 d2161
    hne hbase5 hbase2161
  rwa [sourceBadQAbsLog_actual_eq_sourceBadQAbsLog] at h

/-- **Conditional hcomp.**  The two actual per-place data imply the concrete
source comparison once the Gaussian coefficient bound
log 5 * (W / card) <= 2 log 5 is supplied.  This is S2681's
concreteComparison_iff_weightSum_le_badQAbsLog applied to the bad-q lower
bound; hcomp is not asserted unconditionally. -/
theorem concreteSourceComparison_of_twoPlaces
    {l : PrimeGeFive} {X : Type uX} {label : Type uLabel} [Fintype label]
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
    (D : SourcePilotRegionDonors (l := l) (V := FinitePrimePlace 2 7) I)
    (P : PaperSignedHull X label)
    (hP : P.procession.average =
      (c3ThetaSignedProcession (signedC3 I D)).average)
    (d5 d2161 : S2689ActualBadQPlace I.initial.reduction)
    (hne : d5.b ≠ d2161.b)
    (hbase5 : d5.base = 5) (hbase2161 : d2161.base = 2161)
    (hcoeff : Real.log (5 : ℝ) *
        (sourceThetaWeightSum l / (c3ThetaCard (l := l) : ℝ)) ≤
      2 * Real.log 5) :
    concreteSourceComparison (O I) P := by
  refine (concreteComparison_iff_weightSum_le_badQAbsLog I D P hP).mpr ?_
  have hbad := two_mul_log5_le_sourceBadQAbsLog_actual I.initial d5 d2161
    hne hbase5 hbase2161
  rw [sourceBadQAbsLog_actual_eq_sourceBadQAbsLog] at hbad
  exact le_trans hcoeff hbad

/-- At l.value = 5 the coefficient hypothesis is the proved identity
W / card = 2, so the conditional hcomp needs no numeric side condition. -/
theorem concreteSourceComparison_of_twoPlaces_five
    {l : PrimeGeFive} {X : Type uX} {label : Type uLabel} [Fintype label]
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
    (D : SourcePilotRegionDonors (l := l) (V := FinitePrimePlace 2 7) I)
    (P : PaperSignedHull X label)
    (hP : P.procession.average =
      (c3ThetaSignedProcession (signedC3 I D)).average)
    (d5 d2161 : S2689ActualBadQPlace I.initial.reduction)
    (hne : d5.b ≠ d2161.b)
    (hbase5 : d5.base = 5) (hbase2161 : d2161.base = 2161)
    (hl : l.value = 5) :
    concreteSourceComparison (O I) P :=
  concreteSourceComparison_of_twoPlaces I D P hP d5 d2161 hne
    hbase5 hbase2161
    (by rw [weightSum_div_card_eq_two_of_value_eq_five hl]; linarith)

/-! ## 6. The exact missing actual data -/

/-- The exact missing actual arithmetic datum: an actual bad moduli place over
2161 (i.e. an Fmod-place of residue characteristic 2161 lying in the actual
bad set S2688BadFmodSet, with a proved multiplicative reduction at some
F-place above it).  This is verbatim S2688HasBadPlace2161; it is not an
assumption of any theorem above and it has no inhabitant in the tree. -/
abbrev MissingActualBadPlace2161 (l : PrimeGeFive) : Prop :=
  S2688HasBadPlace2161 l

/-- No place of residue characteristic 2161 belongs to the synthetic
S1280Selection bad set, whose only bad moduli place is the five place. -/
theorem not_mem_selection_of_residueCharacteristic_2161
    (l : PrimeGeFive)
    (p : NumberField.FinitePlace (S1280Arithmetic l).Fmod)
    (hchar : NumberFieldFinitePlace.residueCharacteristic p = 2161) :
    p ∉ (S1280Selection l).V_mod_bad := by
  intro hp
  have hmem : p ∈ ({concreteGaussianFivePlace} :
      Set (NumberField.FinitePlace (S1280Arithmetic l).Fmod)) := by
    rw [S1280Selection_V_mod_bad] at hp
    exact hp
  have hp_eq : p = concreteGaussianFivePlace := Set.eq_of_mem_singleton hmem
  have h5 : NumberFieldFinitePlace.residueCharacteristic p = 5 := by
    rw [hp_eq]
    simpa [S1280Place] using S1280Place_residueCharacteristic l
  rw [hchar] at h5
  norm_num at h5

/-- A hypothetical actual bad place over 2161 (the unproved
S2688HasBadPlace2161) is not one of the selected places of S1280Selection.
Hence the actual Definition 3.1 selection cannot supply the second per-place
datum of the lower bound. -/
theorem hasBadPlace2161_not_selected
    (l : PrimeGeFive) (h : S2688HasBadPlace2161 l) :
    ∃ p : NumberField.FinitePlace (S1280Arithmetic l).Fmod,
      p ∈ S2688BadFmodSet l ∧
      p ∉ (S1280Selection l).V_mod_bad ∧
      NumberFieldFinitePlace.residueCharacteristic p = 2161 := by
  obtain ⟨p, hpbad, hpchar⟩ := h
  exact ⟨p, hpbad, not_mem_selection_of_residueCharacteristic_2161 l p hpchar, hpchar⟩

/-- The synthetic S1280Selection has no bad place of residue characteristic
2161: its V_mod_bad is the singleton five place. -/
theorem S1280Selection_no_2161_badPlace (l : PrimeGeFive) :
    ¬ ∃ p : NumberField.FinitePlace (S1280Arithmetic l).Fmod,
        p ∈ (S1280Selection l).V_mod_bad ∧
        NumberFieldFinitePlace.residueCharacteristic p = 2161 := by
  rintro ⟨p, hp, hchar⟩
  exact not_mem_selection_of_residueCharacteristic_2161 l p hchar hp

/-- The synthetic S1280Selection cannot supply two distinct bad indices; the
two-place conditional theorem therefore has no instance on it. -/
theorem S1280Selection_no_two_badPlaces (l : PrimeGeFive) :
    ¬ ∃ b1 b2 : Bad (S1280Selection l), b1 ≠ b2 := by
  letI : Subsingleton (Bad (S1280Selection l)) := S1280Bad_subsingleton l
  rintro ⟨b1, b2, hne⟩
  exact hne (Subsingleton.elim b1 b2)

/-! ## 7. Axiom audit -/

#print axioms sourceBadQAbsLog_actual_eq_sourceBadQAbsLog
#print axioms sourceBadQAbsLog_actual_nonneg
#print axioms log_le_abs_log_inv_pow
#print axioms log_residueNormBase_le_localLogMagnitude
#print axioms log_residueNormBase_le_abs_log_norm
#print axioms log_residueCharacteristic_le_abs_log_badPlaceQProxy
#print axioms residueNormBase_fivePlace
#print axioms actualFivePlace_abs_log_qParameter
#print axioms actualFivePlace_log_le
#print axioms onePlace_log_le_of_data
#print axioms log5_add_log2161_le_sourceBadQAbsLog_actual
#print axioms log5_add_log2161_le_sourceBadQAbsLog_actual_of_abs
#print axioms two_mul_log5_le_sourceBadQAbsLog_actual
#print axioms hcompSourceBadQData_of_twoPlaces
#print axioms concreteSourceComparison_of_twoPlaces
#print axioms concreteSourceComparison_of_twoPlaces_five
#print axioms hasBadPlace2161_not_selected
#print axioms S1280Selection_no_2161_badPlace
#print axioms S1280Selection_no_two_badPlaces

end LeanFormal.IUT.XiFPaper.S2689SourceBadQAbsLogActual

end
