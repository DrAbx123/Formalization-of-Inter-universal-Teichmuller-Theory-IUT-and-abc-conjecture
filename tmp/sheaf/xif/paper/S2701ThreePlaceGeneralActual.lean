import tmp.sheaf.xif.paper.S2700TwoPlaceGeneralActual
import tmp.sheaf.xif.paper.S2689SourceBadQAbsLogActual

/-!
# S2701: the three-place log-volume lower bound and the sourceBadQAbsLog bridge

Layer: general finite-place log-volume lower bounds (continuation of
S2700TwoPlaceGeneralActual), consumer: the source bad-q absolute log
Theorem311Source.sourceBadQAbsLog and the hcomp bad-q data
S2681HcompMinimalInputActual.HcompBadQData.

## What is proved here

* S2701ThreePlaceLogVolume q5 q2161a q2161b is the three-term volume
  |log ||q5||| + |log ||q2161a||| + |log ||q2161b|||.

* S2701_threePlace_ge: log 5 + 2 * log 2161 <= S2701ThreePlaceLogVolume,
  by S2700_five_log_le_abs_log and two applications of
  S2700_2161_log_le_abs_log.

* S2701_threePlace_gt_two_log5: 2 * log 5 < S2701ThreePlaceLogVolume.

* S2701_threePlace_le_sourceBadQAbsLog: if three bad places of an actual
  source datum S have q-parameter absolute logs dominating the three
  candidate summands (the explicit hypothesis hsrc), then the volume is at
  most the actual per-place source sum sourceBadQAbsLog S.

* S2701_log5_add_two_log2161_le_sourceBadQAbsLog and
  S2701_two_log5_le_sourceBadQAbsLog: the corresponding lower bounds for the
  actual source scalar sourceBadQAbsLog S.

* S2701_hcompBadQData_of_threePlaces: given the explicit source-to-native
  alignment inequality sourceBadQAbsLog I.initial <= baseQTotalLogMagnitude T,
  the three-place source bound yields the S2681 hcomp bad-q data
  HcompBadQData T (i.e. 2 * log 5 <= baseQTotalLogMagnitude T).

* S2701_hcompSourceBadQData_of_threePlaces: the same source bound in the
  S2681 source-side form HcompSourceBadQData I.

* S2701_concreteSourceComparison_of_threePlaces: the conditional hcomp
  conclusion, via S2681's exact numeric reduction
  concreteComparison_iff_weightSum_le_badQAbsLog, under the Gaussian
  coefficient hypothesis log 5 * (W / card) <= log 5 + 2 * log 2161.

* S2701_concreteSourceComparison_of_threePlaces_twoLog5: the conditional
  hcomp conclusion under the S2681 standard coefficient hypothesis
  log 5 * (W / card) <= 2 * log 5.

* S2701_concreteSourceComparison_via_hcompBadQData: the conditional hcomp
  conclusion routed through HcompBadQData T, the alignment inequality and
  the source q agreement, under the same coefficient hypothesis.

## The two 2161 candidates

The two 2161 summands are two arbitrary FinitePlaceQCandidates at the same
place S2696GaussianPlace.  They are allowed to be equal: the volume bound
does not need distinctness, because S2700_2161_log_le_abs_log bounds each
summand separately and the volume counts both occurrences with multiplicity.
Distinctness is needed only on the source side, where the three summands are
three distinct bad indices of the finset sum sourceBadQAbsLog; this is the
explicit hypothesis hb5a, hb5b, hb2161, and it is a genuine constraint on the
source bad-index set.

## What is not claimed

The candidate-to-source identification hsrc is a hypothesis, not proved.
The synthetic S1280Selection has only the five place (S2689): its V_mod_bad
is the singleton {concreteGaussianFivePlace}, and no actual bad place of
residue characteristic 2161 with an actual source q-parameter exists in the
tree (S2688HasBadPlace2161 has no inhabitant).  Hence hsrc cannot be
instantiated from current actual source data; the exact missing bridge is the
actual 2161 bad place together with its q-parameter/order normalization, which
is the missing datum already recorded by S2689 section 6.  The stale
S2696VbadActual is not imported or used anywhere in this file.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S2696GaussianPlace2161Actual
open LeanFormal.IUT.XiFPaper.S2700TwoPlaceGeneralActual
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual
open LeanFormal.IUT.XiFPaper.S2698ResidueNorm2161Actual
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.ThetaPacketQIdentificationActual
open LeanFormal.IUT.XiFPaper.ConcreteThetaLinkSourceActual
open LeanFormal.IUT.XiFPaper.PaperThetaMagnitudeSignedActual
open LeanFormal.IUT.XiFPaper.ProcessionThetaPacketAverageActual
open LeanFormal.IUT.XiFPaper.S1931SourceHaarSignedAverageActual
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.S2679HcompLocalBoundsActual
open LeanFormal.IUT.XiFPaper.S2681HcompMinimalInputActual

namespace LeanFormal.IUT.XiFPaper.S2701ThreePlaceGeneralActual

universe uX uLabel

local instance s2701GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-! ## 1. The three-place log volume -/

/-- The three-term general finite-place log volume: the five-place candidate
absolute log plus two absolute logs of candidates at the Gaussian 2161 place.
The two 2161 candidates may be equal; no distinctness is used in this
definition or in the lower bound below. -/
noncomputable def S2701ThreePlaceLogVolume
    (q5 : FinitePlaceQCandidate concreteGaussianFivePlace)
    (q2161a q2161b : FinitePlaceQCandidate S2696GaussianPlace) : ℝ :=
  |Real.log ‖q5.q‖| + |Real.log ‖q2161a.q‖| + |Real.log ‖q2161b.q‖|

/-- Three-place lower bound.  log 5 + 2 * log 2161 is bounded by the
three-term volume.  The five summand comes from
S2700_five_log_le_abs_log; each of the two 2161 summands is bounded
separately by S2700_2161_log_le_abs_log. -/
theorem S2701_threePlace_ge
    (q5 : FinitePlaceQCandidate concreteGaussianFivePlace)
    (q2161a q2161b : FinitePlaceQCandidate S2696GaussianPlace) :
    Real.log (5 : ℝ) + 2 * Real.log (2161 : ℝ) ≤
      S2701ThreePlaceLogVolume q5 q2161a q2161b := by
  have h5 := S2700_five_log_le_abs_log q5
  have h1 := S2700_2161_log_le_abs_log q2161a
  have h2 := S2700_2161_log_le_abs_log q2161b
  unfold S2701ThreePlaceLogVolume
  linarith

/-- Strict three-place bound.  The three-term volume is strictly bigger
than 2 * log 5, since log 5 < log 2161 and log 2161 > 0. -/
theorem S2701_threePlace_gt_two_log5
    (q5 : FinitePlaceQCandidate concreteGaussianFivePlace)
    (q2161a q2161b : FinitePlaceQCandidate S2696GaussianPlace) :
    2 * Real.log (5 : ℝ) < S2701ThreePlaceLogVolume q5 q2161a q2161b := by
  have hge := S2701_threePlace_ge q5 q2161a q2161b
  have hlt : Real.log (5 : ℝ) < Real.log (2161 : ℝ) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  have hpos : 0 < Real.log (2161 : ℝ) := Real.log_pos (by norm_num)
  linarith

/-! ## 2. Three distinct bad places in an actual source datum -/

/-- Three distinct indices below a finset sum: for a nonnegative summand
function, the sum of the three values is bounded by the total sum. -/
theorem three_terms_le_sum {α : Type*} [Fintype α] (f : α → ℝ)
    (hf : ∀ a, 0 ≤ f a) {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    f a + f b + f c ≤ ∑ x : α, f x := by
  classical
  have hsub : ({a, b, c} : Finset α) ⊆ Finset.univ := Finset.subset_univ _
  have h := Finset.sum_le_sum_of_subset_of_nonneg (f := f) hsub
    (fun x _ _ => hf x)
  have hsum : (∑ x ∈ ({a, b, c} : Finset α), f x) = f a + f b + f c := by
    simp [Finset.sum_insert, hab, hac, hbc, add_assoc]
  rw [hsum] at h
  exact h

/-- Candidate-to-source comparison.  If the three candidate absolute logs
are dominated by the actual source q-parameter absolute logs at three distinct
bad places of S, then the three-place volume is at most the actual per-place
source sum sourceBadQAbsLog S.  The hypothesis hsrc is explicit: no
identification of the candidates with source q-parameters is asserted. -/
theorem S2701_threePlace_le_sourceBadQAbsLog
    {l : PrimeGeFive} (S : SourceDefinition31Data l)
    (q5 : FinitePlaceQCandidate concreteGaussianFivePlace)
    (q2161a q2161b : FinitePlaceQCandidate S2696GaussianPlace)
    (b5 b2161a b2161b : S.badPlaces)
    (hb5a : b5 ≠ b2161a) (hb5b : b5 ≠ b2161b) (hb2161 : b2161a ≠ b2161b)
    (hsrc5 : |Real.log ‖q5.q‖| ≤
      |Real.log (S.reduction.qParameter b5)|)
    (hsrc1 : |Real.log ‖q2161a.q‖| ≤
      |Real.log (S.reduction.qParameter b2161a)|)
    (hsrc2 : |Real.log ‖q2161b.q‖| ≤
      |Real.log (S.reduction.qParameter b2161b)|) :
    S2701ThreePlaceLogVolume q5 q2161a q2161b ≤ sourceBadQAbsLog S := by
  unfold S2701ThreePlaceLogVolume
  unfold sourceBadQAbsLog
  letI := S.bad_finite
  have hsum := three_terms_le_sum
    (fun b : S.badPlaces => |Real.log (S.reduction.qParameter b)|)
    (fun b => abs_nonneg _) hb5a hb5b hb2161
  linarith

/-- The source-side three-place lower bound.  log 5 + 2 * log 2161 is
bounded by the actual source bad-q absolute log, under the explicit
candidate-to-source comparison hsrc at three distinct bad places. -/
theorem S2701_log5_add_two_log2161_le_sourceBadQAbsLog
    {l : PrimeGeFive} (S : SourceDefinition31Data l)
    (q5 : FinitePlaceQCandidate concreteGaussianFivePlace)
    (q2161a q2161b : FinitePlaceQCandidate S2696GaussianPlace)
    (b5 b2161a b2161b : S.badPlaces)
    (hb5a : b5 ≠ b2161a) (hb5b : b5 ≠ b2161b) (hb2161 : b2161a ≠ b2161b)
    (hsrc5 : |Real.log ‖q5.q‖| ≤
      |Real.log (S.reduction.qParameter b5)|)
    (hsrc1 : |Real.log ‖q2161a.q‖| ≤
      |Real.log (S.reduction.qParameter b2161a)|)
    (hsrc2 : |Real.log ‖q2161b.q‖| ≤
      |Real.log (S.reduction.qParameter b2161b)|) :
    Real.log (5 : ℝ) + 2 * Real.log (2161 : ℝ) ≤ sourceBadQAbsLog S :=
  le_trans (S2701_threePlace_ge q5 q2161a q2161b)
    (S2701_threePlace_le_sourceBadQAbsLog S q5 q2161a q2161b
      b5 b2161a b2161b hb5a hb5b hb2161 hsrc5 hsrc1 hsrc2)

/-- The 2 log 5 source bound.  In particular the actual source bad-q
absolute log dominates 2 * log 5. -/
theorem S2701_two_log5_le_sourceBadQAbsLog
    {l : PrimeGeFive} (S : SourceDefinition31Data l)
    (q5 : FinitePlaceQCandidate concreteGaussianFivePlace)
    (q2161a q2161b : FinitePlaceQCandidate S2696GaussianPlace)
    (b5 b2161a b2161b : S.badPlaces)
    (hb5a : b5 ≠ b2161a) (hb5b : b5 ≠ b2161b) (hb2161 : b2161a ≠ b2161b)
    (hsrc5 : |Real.log ‖q5.q‖| ≤
      |Real.log (S.reduction.qParameter b5)|)
    (hsrc1 : |Real.log ‖q2161a.q‖| ≤
      |Real.log (S.reduction.qParameter b2161a)|)
    (hsrc2 : |Real.log ‖q2161b.q‖| ≤
      |Real.log (S.reduction.qParameter b2161b)|) :
    2 * Real.log (5 : ℝ) ≤ sourceBadQAbsLog S := by
  have h := S2701_log5_add_two_log2161_le_sourceBadQAbsLog S q5 q2161a q2161b
    b5 b2161a b2161b hb5a hb5b hb2161 hsrc5 hsrc1 hsrc2
  have hlt : Real.log (5 : ℝ) < Real.log (2161 : ℝ) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  have hpos : 0 < Real.log (2161 : ℝ) := Real.log_pos (by norm_num)
  linarith

/-! ## 3. The S2681 hcomp bad-q data -/

/-- Conditional HcompBadQData.  The three-place source bound plus the
explicit alignment inequality
sourceBadQAbsLog I.initial <= baseQTotalLogMagnitude T yields the S2681
bad-q data HcompBadQData T, i.e. 2 * log 5 <= baseQTotalLogMagnitude T.
The alignment is a hypothesis; the actual source/native identification is
not proved and is not asserted. -/
theorem S2701_hcompBadQData_of_threePlaces
    {l : PrimeGeFive}
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    (q5 : FinitePlaceQCandidate concreteGaussianFivePlace)
    (q2161a q2161b : FinitePlaceQCandidate S2696GaussianPlace)
    (b5 b2161a b2161b : I.initial.badPlaces)
    (hb5a : b5 ≠ b2161a) (hb5b : b5 ≠ b2161b) (hb2161 : b2161a ≠ b2161b)
    (hsrc5 : |Real.log ‖q5.q‖| ≤
      |Real.log (I.initial.reduction.qParameter b5)|)
    (hsrc1 : |Real.log ‖q2161a.q‖| ≤
      |Real.log (I.initial.reduction.qParameter b2161a)|)
    (hsrc2 : |Real.log ‖q2161b.q‖| ≤
      |Real.log (I.initial.reduction.qParameter b2161b)|)
    (halign : sourceBadQAbsLog I.initial ≤ baseQTotalLogMagnitude T) :
    HcompBadQData T := by
  unfold HcompBadQData
  have h := S2701_two_log5_le_sourceBadQAbsLog I.initial q5 q2161a q2161b
    b5 b2161a b2161b hb5a hb5b hb2161 hsrc5 hsrc1 hsrc2
  linarith

/-- Conditional hcomp.  The three-place source bound and the Gaussian
coefficient hypothesis
log 5 * (W / card) <= log 5 + 2 * log 2161 imply the concrete source
comparison (hcomp), via S2681's exact numeric reduction.  Both the candidate
comparison and the coefficient bound are explicit hypotheses; no
unconditional hcomp is asserted. -/
theorem S2701_concreteSourceComparison_of_threePlaces
    {l : PrimeGeFive} {X : Type uX} {label : Type uLabel} [Fintype label]
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
    (D : SourcePilotRegionDonors (l := l) (V := FinitePrimePlace 2 7) I)
    (P : PaperSignedHull X label)
    (hP : P.procession.average =
      (c3ThetaSignedProcession (signedC3 I D)).average)
    (q5 : FinitePlaceQCandidate concreteGaussianFivePlace)
    (q2161a q2161b : FinitePlaceQCandidate S2696GaussianPlace)
    (b5 b2161a b2161b : I.initial.badPlaces)
    (hb5a : b5 ≠ b2161a) (hb5b : b5 ≠ b2161b) (hb2161 : b2161a ≠ b2161b)
    (hsrc5 : |Real.log ‖q5.q‖| ≤
      |Real.log (I.initial.reduction.qParameter b5)|)
    (hsrc1 : |Real.log ‖q2161a.q‖| ≤
      |Real.log (I.initial.reduction.qParameter b2161a)|)
    (hsrc2 : |Real.log ‖q2161b.q‖| ≤
      |Real.log (I.initial.reduction.qParameter b2161b)|)
    (hcoeff : Real.log (5 : ℝ) *
        (sourceThetaWeightSum l / (c3ThetaCard (l := l) : ℝ)) ≤
      Real.log (5 : ℝ) + 2 * Real.log (2161 : ℝ)) :
    concreteSourceComparison (O I) P := by
  refine (concreteComparison_iff_weightSum_le_badQAbsLog I D P hP).mpr ?_
  have hsrc := S2701_log5_add_two_log2161_le_sourceBadQAbsLog I.initial
    q5 q2161a q2161b b5 b2161a b2161b hb5a hb5b hb2161 hsrc5 hsrc1 hsrc2
  linarith

/-- The S2681 source-side bad-q data from the three-place bound:
2 * log 5 <= sourceBadQAbsLog I.initial.  This is exactly the proposition
HcompSourceBadQData I. -/
theorem S2701_hcompSourceBadQData_of_threePlaces
    {l : PrimeGeFive}
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
    (q5 : FinitePlaceQCandidate concreteGaussianFivePlace)
    (q2161a q2161b : FinitePlaceQCandidate S2696GaussianPlace)
    (b5 b2161a b2161b : I.initial.badPlaces)
    (hb5a : b5 ≠ b2161a) (hb5b : b5 ≠ b2161b) (hb2161 : b2161a ≠ b2161b)
    (hsrc5 : |Real.log ‖q5.q‖| ≤
      |Real.log (I.initial.reduction.qParameter b5)|)
    (hsrc1 : |Real.log ‖q2161a.q‖| ≤
      |Real.log (I.initial.reduction.qParameter b2161a)|)
    (hsrc2 : |Real.log ‖q2161b.q‖| ≤
      |Real.log (I.initial.reduction.qParameter b2161b)|) :
    HcompSourceBadQData I := by
  unfold HcompSourceBadQData
  exact S2701_two_log5_le_sourceBadQAbsLog I.initial q5 q2161a q2161b
    b5 b2161a b2161b hb5a hb5b hb2161 hsrc5 hsrc1 hsrc2

/-- Conditional hcomp with the S2681 standard coefficient hypothesis
log 5 * (W / card) <= 2 * log 5.  The three-place source bound
2 * log 5 <= sourceBadQAbsLog I.initial alone closes the numeric inequality;
no native data or alignment is used. -/
theorem S2701_concreteSourceComparison_of_threePlaces_twoLog5
    {l : PrimeGeFive} {X : Type uX} {label : Type uLabel} [Fintype label]
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
    (D : SourcePilotRegionDonors (l := l) (V := FinitePrimePlace 2 7) I)
    (P : PaperSignedHull X label)
    (hP : P.procession.average =
      (c3ThetaSignedProcession (signedC3 I D)).average)
    (q5 : FinitePlaceQCandidate concreteGaussianFivePlace)
    (q2161a q2161b : FinitePlaceQCandidate S2696GaussianPlace)
    (b5 b2161a b2161b : I.initial.badPlaces)
    (hb5a : b5 ≠ b2161a) (hb5b : b5 ≠ b2161b) (hb2161 : b2161a ≠ b2161b)
    (hsrc5 : |Real.log ‖q5.q‖| ≤
      |Real.log (I.initial.reduction.qParameter b5)|)
    (hsrc1 : |Real.log ‖q2161a.q‖| ≤
      |Real.log (I.initial.reduction.qParameter b2161a)|)
    (hsrc2 : |Real.log ‖q2161b.q‖| ≤
      |Real.log (I.initial.reduction.qParameter b2161b)|)
    (hcoeff : Real.log (5 : ℝ) *
        (sourceThetaWeightSum l / (c3ThetaCard (l := l) : ℝ)) ≤
      2 * Real.log (5 : ℝ)) :
    concreteSourceComparison (O I) P := by
  refine (concreteComparison_iff_weightSum_le_badQAbsLog I D P hP).mpr ?_
  have h2 := S2701_two_log5_le_sourceBadQAbsLog I.initial q5 q2161a q2161b
    b5 b2161a b2161b hb5a hb5b hb2161 hsrc5 hsrc1 hsrc2
  linarith

/-- Conditional hcomp routed through the S2681 bad-q data.  The three-place
source bound plus the alignment inequality yield HcompBadQData T
(S2701_hcompBadQData_of_threePlaces); S2681's hcomp_of_agreement_badQ then
gives hcomp from the source q agreement and the standard coefficient
hypothesis.  The q agreement, the alignment and the coefficient bound are
explicit hypotheses. -/
theorem S2701_concreteSourceComparison_via_hcompBadQData
    {l : PrimeGeFive} {X : Type uX} {label : Type uLabel} [Fintype label]
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
    (D : SourcePilotRegionDonors (l := l) (V := FinitePrimePlace 2 7) I)
    (P : PaperSignedHull X label)
    (hP : P.procession.average =
      (c3ThetaSignedProcession (signedC3 I D)).average)
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    (q5 : FinitePlaceQCandidate concreteGaussianFivePlace)
    (q2161a q2161b : FinitePlaceQCandidate S2696GaussianPlace)
    (b5 b2161a b2161b : I.initial.badPlaces)
    (hb5a : b5 ≠ b2161a) (hb5b : b5 ≠ b2161b) (hb2161 : b2161a ≠ b2161b)
    (hsrc5 : |Real.log ‖q5.q‖| ≤
      |Real.log (I.initial.reduction.qParameter b5)|)
    (hsrc1 : |Real.log ‖q2161a.q‖| ≤
      |Real.log (I.initial.reduction.qParameter b2161a)|)
    (hsrc2 : |Real.log ‖q2161b.q‖| ≤
      |Real.log (I.initial.reduction.qParameter b2161b)|)
    (halign : sourceBadQAbsLog I.initial ≤ baseQTotalLogMagnitude T)
    (hQ : HcompSourceQAgreement I T)
    (hcoeff : Real.log (5 : ℝ) *
        (sourceThetaWeightSum l / (c3ThetaCard (l := l) : ℝ)) ≤
      2 * Real.log (5 : ℝ)) :
    concreteSourceComparison (O I) P :=
  hcomp_of_agreement_badQ I D P T hP hQ
    (S2701_hcompBadQData_of_threePlaces I T q5 q2161a q2161b
      b5 b2161a b2161b hb5a hb5b hb2161 hsrc5 hsrc1 hsrc2 halign)
    hcoeff

/-! ## 4. Checks and axiom audit -/

#check S2701ThreePlaceLogVolume
#check S2701_threePlace_ge
#check S2701_threePlace_gt_two_log5
#check S2701_threePlace_le_sourceBadQAbsLog
#check S2701_log5_add_two_log2161_le_sourceBadQAbsLog
#check S2701_two_log5_le_sourceBadQAbsLog
#check S2701_hcompBadQData_of_threePlaces
#check S2701_hcompSourceBadQData_of_threePlaces
#check S2701_concreteSourceComparison_of_threePlaces
#check S2701_concreteSourceComparison_of_threePlaces_twoLog5
#check S2701_concreteSourceComparison_via_hcompBadQData

#print axioms S2701_threePlace_ge
#print axioms S2701_threePlace_gt_two_log5
#print axioms S2701_threePlace_le_sourceBadQAbsLog
#print axioms S2701_log5_add_two_log2161_le_sourceBadQAbsLog
#print axioms S2701_two_log5_le_sourceBadQAbsLog
#print axioms S2701_hcompBadQData_of_threePlaces
#print axioms S2701_hcompSourceBadQData_of_threePlaces
#print axioms S2701_concreteSourceComparison_of_threePlaces
#print axioms S2701_concreteSourceComparison_of_threePlaces_twoLog5
#print axioms S2701_concreteSourceComparison_via_hcompBadQData

end LeanFormal.IUT.XiFPaper.S2701ThreePlaceGeneralActual
end
