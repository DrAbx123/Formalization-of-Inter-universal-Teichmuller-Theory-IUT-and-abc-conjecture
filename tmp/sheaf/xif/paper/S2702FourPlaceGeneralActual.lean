/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import tmp.sheaf.xif.paper.S2700TwoPlaceGeneralActual
import tmp.sheaf.xif.paper.S2689SourceBadQAbsLogActual
import tmp.sheaf.xif.paper.S2681HcompMinimalInputActual

/-!
# S2702: the four-place q-side lower bound

The paper's V_bad for the Gaussian example carries two places above 5 and two
places above 2161.  This file proves the corresponding four-place lower bound
on the actual q-side log volume:

  2 * log 5 + 2 * log 2161 <= |log q_{5a}| + |log q_{5b}|
                              + |log q_{2161a}| + |log q_{2161b}|,

and the strict consequence 2 * log 5 < that sum (because log 5 < log 2161).
The four summands are arbitrary actual completion q-candidates at the concrete
Gaussian five place and at the actual Gaussian place above 2161.

The second half connects the lower bound to the actual source scalar
sourceBadQAbsLog S.  Since the current tree has no actual source selection
carrying four distinct bad indices with the two 5-places and the two 2161
places, that identification is kept as an explicit hypothesis
S2702FourPlaceSourceData S: four bad indices with pairwise distinctness and
the four pointwise lower bounds.  From it we prove

  sourceBadQAbsLog S >= 2 log 5 + 2 log 2161,   sourceBadQAbsLog S >= 2 log 5,

and, conditionally on the source/native alignment inequality
sourceBadQAbsLog I.initial <= baseQTotalLogMagnitude T, the S2681 bad-q datum
HcompBadQData T.  No equality between the four-place source datum and the
native base-q family is asserted: S2696VbadActual is stale/broken and its
four-place variant sits on top of it, so the bridge remains the explicit
hypothesis reported in the final section.

No unsound placeholder, no added assumption, no machine-code evaluation,
and no vacuous witness is used.
-/

noncomputable section

open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2702FourPlaceGeneralActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S2696GaussianPlace2161Actual
open LeanFormal.IUT.XiFPaper.S2698ResidueNorm2161Actual
open LeanFormal.IUT.XiFPaper.S2700TwoPlaceGeneralActual
open LeanFormal.IUT.XiFPaper.S2689SourceBadQAbsLogActual
open LeanFormal.IUT.XiFPaper.S2681HcompMinimalInputActual
open LeanFormal.IUT.XiFPaper.ConcreteThetaLinkSourceActual
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.ProcessionThetaPacketAverageActual
open LeanFormal.IUT.XiFPaper.S1931SourceHaarSignedAverageActual

local instance s2702GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-! ## 1. The four-place q-side log volume -/

/-- The four-place q-side log volume: the absolute logarithms of four actual
completion q-candidates, two at the concrete Gaussian five place and two at the
actual Gaussian place above 2161. -/
noncomputable def S2702FourPlaceLogVolume
    (q5a q5b : FinitePlaceQCandidate concreteGaussianFivePlace)
    (q2161a q2161b : FinitePlaceQCandidate S2696GaussianPlace) : ℝ :=
  |Real.log ‖q5a.q‖| + |Real.log ‖q5b.q‖| +
    |Real.log ‖q2161a.q‖| + |Real.log ‖q2161b.q‖|

/-- Four-place lower bound.  Each of the two five-place terms is at least
log 5 and each of the two 2161-place terms is at least log 2161, by the actual
per-place order formula of S2700. -/
theorem S2702_fourPlace_ge
    (q5a q5b : FinitePlaceQCandidate concreteGaussianFivePlace)
    (q2161a q2161b : FinitePlaceQCandidate S2696GaussianPlace) :
    2 * Real.log (5 : ℝ) + 2 * Real.log (2161 : ℝ) ≤
      S2702FourPlaceLogVolume q5a q5b q2161a q2161b := by
  have h5a := S2700_five_log_le_abs_log q5a
  have h5b := S2700_five_log_le_abs_log q5b
  have h2161a := S2700_2161_log_le_abs_log q2161a
  have h2161b := S2700_2161_log_le_abs_log q2161b
  unfold S2702FourPlaceLogVolume
  linarith

/-- Strictness.  The four-place volume is strictly larger than 2 log 5,
because log 5 < log 2161 and log 5 > 0. -/
theorem S2702_fourPlace_gt_two_log5
    (q5a q5b : FinitePlaceQCandidate concreteGaussianFivePlace)
    (q2161a q2161b : FinitePlaceQCandidate S2696GaussianPlace) :
    2 * Real.log (5 : ℝ) <
      S2702FourPlaceLogVolume q5a q5b q2161a q2161b := by
  have hge := S2702_fourPlace_ge q5a q5b q2161a q2161b
  have h5pos : (0 : ℝ) < Real.log (5 : ℝ) := Real.log_pos (by norm_num)
  have hlt : Real.log (5 : ℝ) < Real.log (2161 : ℝ) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  linarith

/-! ## 2. Four actual bad places and the source scalar -/

/-- The explicit actual source hypothesis used by this file: four bad indices
of the source reduction clause, pairwise distinct, carrying the two 5-bounds
and the two 2161-bounds on the absolute q-parameter logarithm.

This is the exact source-data identification that the current tree does not
supply: the synthetic S1280Selection has a subsingleton bad index type and no
place of residue characteristic 2161, while S2696VbadActual (and the four-place
file on top of it) is stale/broken and is deliberately not imported here. -/
structure S2702FourPlaceSourceData {l : PrimeGeFive}
    (S : SourceDefinition31Data l) where
  b5a : S.badPlaces
  b5b : S.badPlaces
  b2161a : S.badPlaces
  b2161b : S.badPlaces
  distinct_5a_5b : b5a ≠ b5b
  distinct_5a_2161a : b5a ≠ b2161a
  distinct_5a_2161b : b5a ≠ b2161b
  distinct_5b_2161a : b5b ≠ b2161a
  distinct_5b_2161b : b5b ≠ b2161b
  distinct_2161a_2161b : b2161a ≠ b2161b
  log5a : Real.log (5 : ℝ) ≤ |Real.log (S.reduction.qParameter b5a)|
  log5b : Real.log (5 : ℝ) ≤ |Real.log (S.reduction.qParameter b5b)|
  log2161a : Real.log (2161 : ℝ) ≤ |Real.log (S.reduction.qParameter b2161a)|
  log2161b : Real.log (2161 : ℝ) ≤ |Real.log (S.reduction.qParameter b2161b)|

/-- Four distinct summands with nonnegative values are bounded by the full
finite sum. -/
theorem S2702_four_terms_le_sum {α : Type*} [Fintype α]
    (f : α → ℝ) (hf : ∀ a, 0 ≤ f a)
    {a b c d : α} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    f a + f b + f c + f d ≤ ∑ x, f x := by
  classical
  have hsub : ({a, b, c, d} : Finset α) ⊆ Finset.univ := Finset.subset_univ _
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun x _ _ => hf x)
  have ha : a ∉ ({b, c, d} : Finset α) := by simp [hab, hac, had]
  have hb : b ∉ ({c, d} : Finset α) := by simp [hbc, hbd]
  have hc : c ∉ ({d} : Finset α) := by simp [hcd]
  have hsum : Finset.sum ({a, b, c, d} : Finset α) f =
      f a + f b + f c + f d := by
    rw [Finset.sum_insert ha, Finset.sum_insert hb, Finset.sum_insert hc,
      Finset.sum_singleton]
    ring
  rw [hsum] at hle
  exact hle

/-- Four-place source lower bound.  From four pairwise distinct actual bad
indices with the four pointwise bounds, the actual source bad-q absolute log is
at least 2 log 5 + 2 log 2161.  No singleton substitution is made: the sum is
over the actual bad index type S.badPlaces. -/
theorem S2702_sourceBadQAbsLog_ge_fourPlace
    {l : PrimeGeFive} (S : SourceDefinition31Data l)
    (hsrc : S2702FourPlaceSourceData S) :
    2 * Real.log (5 : ℝ) + 2 * Real.log (2161 : ℝ) ≤ sourceBadQAbsLog S := by
  unfold sourceBadQAbsLog
  letI := S.bad_finite
  have h := S2702_four_terms_le_sum
    (fun b : S.badPlaces => |Real.log (S.reduction.qParameter b)|)
    (fun b => abs_nonneg _)
    hsrc.distinct_5a_5b hsrc.distinct_5a_2161a hsrc.distinct_5a_2161b
    hsrc.distinct_5b_2161a hsrc.distinct_5b_2161b hsrc.distinct_2161a_2161b
  linarith [h, hsrc.log5a, hsrc.log5b, hsrc.log2161a, hsrc.log2161b]

/-- The four-place source bound in the per-place form used by
S2689SourceBadQAbsLogActual. -/
theorem S2702_sourceBadQAbsLog_actual_ge_fourPlace
    {l : PrimeGeFive} (S : SourceDefinition31Data l)
    (hsrc : S2702FourPlaceSourceData S) :
    2 * Real.log (5 : ℝ) + 2 * Real.log (2161 : ℝ) ≤
      sourceBadQAbsLog_actual S := by
  rw [sourceBadQAbsLog_actual_eq_sourceBadQAbsLog]
  exact S2702_sourceBadQAbsLog_ge_fourPlace S hsrc

/-- The 2 log 5 source bound.  The four-place bound implies the two-place
source bound 2 log 5 <= sourceBadQAbsLog S. -/
theorem S2702_sourceBadQAbsLog_ge_two_log5
    {l : PrimeGeFive} (S : SourceDefinition31Data l)
    (hsrc : S2702FourPlaceSourceData S) :
    2 * Real.log (5 : ℝ) ≤ sourceBadQAbsLog S := by
  have h := S2702_sourceBadQAbsLog_ge_fourPlace S hsrc
  have h5pos : (0 : ℝ) < Real.log (5 : ℝ) := Real.log_pos (by norm_num)
  have h2161pos : (0 : ℝ) < Real.log (2161 : ℝ) := Real.log_pos (by norm_num)
  linarith

/-- The synthetic singleton selection cannot carry four distinct bad indices:
this is the precise obstruction to instantiating the four-place source datum on
the current concrete source selection. -/
theorem S2702_no_fourPlaceSourceData_of_subsingleton
    {l : PrimeGeFive} (S : SourceDefinition31Data l)
    [Subsingleton S.badPlaces] :
    ¬ Nonempty (S2702FourPlaceSourceData S) := by
  rintro ⟨hsrc⟩
  exact hsrc.distinct_5a_5b (Subsingleton.elim _ _)

/-! ## 3. The S2681 bad-q datum and the concrete comparison -/

universe uX uLabel

/-- The source-side bad-q datum of S2681 (2 log 5 <= sourceBadQAbsLog) from
four-place source data. -/
theorem S2702_hcompSourceBadQData
    {l : PrimeGeFive}
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
    (hsrc : S2702FourPlaceSourceData I.initial) :
    HcompSourceBadQData I := by
  unfold HcompSourceBadQData
  exact S2702_sourceBadQAbsLog_ge_two_log5 I.initial hsrc

/-- Conditional hcomp bad-q datum: the four-place source bound together with
the explicit source/native alignment inequality gives S2681's HcompBadQData T. -/
theorem S2702_hcompBadQData_of_fourPlace
    {l : PrimeGeFive}
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    (hsrc : S2702FourPlaceSourceData I.initial)
    (halign : sourceBadQAbsLog I.initial ≤ baseQTotalLogMagnitude T) :
    HcompBadQData T := by
  unfold HcompBadQData
  have h := S2702_sourceBadQAbsLog_ge_two_log5 I.initial hsrc
  linarith

/-- The concrete source comparison (hcomp) from four-place source data and the
Gaussian coefficient bound, via the S2681 numeric reduction. -/
theorem S2702_concreteSourceComparison_of_fourPlaces
    {l : PrimeGeFive} {X : Type uX} {label : Type uLabel} [Fintype label]
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
    (D : SourcePilotRegionDonors (l := l) (V := FinitePrimePlace 2 7) I)
    (P : PaperSignedHull X label)
    (hP : P.procession.average =
      (c3ThetaSignedProcession (signedC3 I D)).average)
    (hsrc : S2702FourPlaceSourceData I.initial)
    (hcoeff : Real.log (5 : ℝ) *
        (sourceThetaWeightSum l / (c3ThetaCard (l := l) : ℝ)) ≤
      2 * Real.log 5) :
    concreteSourceComparison (O I) P := by
  refine (concreteComparison_iff_weightSum_le_badQAbsLog I D P hP).mpr ?_
  have hbad := S2702_sourceBadQAbsLog_ge_two_log5 I.initial hsrc
  exact le_trans hcoeff hbad

/-- At l.value = 5 the Gaussian coefficient is the proved identity W / card = 2,
so the four-place concrete comparison needs no coefficient side condition. -/
theorem S2702_concreteSourceComparison_of_fourPlaces_five
    {l : PrimeGeFive} {X : Type uX} {label : Type uLabel} [Fintype label]
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
    (D : SourcePilotRegionDonors (l := l) (V := FinitePrimePlace 2 7) I)
    (P : PaperSignedHull X label)
    (hP : P.procession.average =
      (c3ThetaSignedProcession (signedC3 I D)).average)
    (hsrc : S2702FourPlaceSourceData I.initial)
    (hl : l.value = 5) :
    concreteSourceComparison (O I) P :=
  S2702_concreteSourceComparison_of_fourPlaces I D P hP hsrc
    (by rw [weightSum_div_card_eq_two_of_value_eq_five hl]; linarith)

/-- The concrete paper q-pilot scalar is at most the negative of the four-place
lower bound: this is the PaperQPilotObject form of the source bound. -/
theorem S2702_qPilotLogVolume_le_fourPlace
    {l : PrimeGeFive}
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
    (hsrc : S2702FourPlaceSourceData I.initial) :
    (O I).qPilotLogVolume ≤
      -(2 * Real.log (5 : ℝ) + 2 * Real.log (2161 : ℝ)) := by
  have h := S2702_sourceBadQAbsLog_ge_fourPlace I.initial hsrc
  rw [(O I).qPilotLogVolume_eq]
  change -sourceBadQAbsLog I.initial ≤
    -(2 * Real.log (5 : ℝ) + 2 * Real.log (2161 : ℝ))
  linarith

/-! ## 4. The exact missing actual source-data bridge -/

/-- The exact source-data identification missing from the current tree: an
actual source S carrying four distinct bad indices with the two 5-bounds and the
two 2161-bounds.  This is an abbreviation for the hypothesis, not an assertion
of it. -/
abbrev S2702MissingFourPlaceSourceData {l : PrimeGeFive}
    (S : SourceDefinition31Data l) : Prop :=
  Nonempty (S2702FourPlaceSourceData S)

/-! ## 5. Axiom audit -/

#print axioms S2702_fourPlace_ge
#print axioms S2702_fourPlace_gt_two_log5
#print axioms S2702_four_terms_le_sum
#print axioms S2702_sourceBadQAbsLog_ge_fourPlace
#print axioms S2702_sourceBadQAbsLog_actual_ge_fourPlace
#print axioms S2702_sourceBadQAbsLog_ge_two_log5
#print axioms S2702_hcompSourceBadQData
#print axioms S2702_hcompBadQData_of_fourPlace
#print axioms S2702_concreteSourceComparison_of_fourPlaces
#print axioms S2702_concreteSourceComparison_of_fourPlaces_five
#print axioms S2702_qPilotLogVolume_le_fourPlace
#print axioms S2702_no_fourPlaceSourceData_of_subsingleton

end LeanFormal.IUT.XiFPaper.S2702FourPlaceGeneralActual

end
