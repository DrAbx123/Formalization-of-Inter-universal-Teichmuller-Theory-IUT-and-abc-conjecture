/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import tmp.sheaf.xif.paper.S2699LogQ2161Actual
import tmp.sheaf.xif.paper.S2690TwoPlaceBadQActual
import tmp.sheaf.xif.paper.S2681HcompMinimalInputActual

/-!
# S2699: actual two-place bad-q assembly over the Gaussian places above 5 and 2161

## What this file assembles

The actual two-place bad-q absolute log

  sourceBadQAbsLog_twoPlace q2161 = |log ||q_5||| + |log ||q_2161|||

with

* q_5 the actual q-candidate of S2690TwoPlaceBadQActual.q5 at the concrete
  Gaussian five place concreteGaussianFivePlace (residue norm base 5), and
* q_2161 an actual FinitePlaceQCandidate at the canonical Gaussian place
  above 2161, S2696GaussianPlace2161Actual.S2696GaussianPlace.

The 2161-side lower bound is S2699LogQ2161Actual.S2699_log2161_le_abs_log_q,
which applies to *every* q-candidate at that place; the 5-side lower bound is
S2690TwoPlaceBadQActual.q5_abs_log_ge_log5.  Their sum gives

  log 5 + log 2161 <= sourceBadQAbsLog_twoPlace q2161,

and Real.log_lt_log (5 < 2161) upgrades this to the strict bound

  2 * log 5 < sourceBadQAbsLog_twoPlace q2161.

The final conditional theorem feeds the numeric residual and the explicit
two-place/native bridge (halign : sourceBadQAbsLog_twoPlace q2161 <=
baseQTotalLogMagnitude T) into S2681HcompMinimalInputActual.HcompBadQData T
(2 * log 5 <= baseQTotalLogMagnitude T), the bad-q datum consumed by S2681 and
S2678.  The bridge itself is not asserted; it remains an explicit hypothesis.

## Place alignment note

The current S2696 place is S2696GaussianPlace (namespace
S2696GaussianPlace2161Actual).  An older alias
S2696VbadActual.S2696GaussianPlace2161 still occurs in the type of
S2699SourceQv2161Actual.S2699Candidate, but it is not present in the current
S2696VbadActual source.  Because S2699_log2161_le_abs_log_q is stated for
S2696GaussianPlace and holds for an arbitrary candidate there, this file
quantifies over q2161 : FinitePlaceQCandidate S2696GaussianPlace; this is
strictly stronger than fixing one classical choice, and no singleton
substitution or alias is used.

No sorry, admit, axiom, native_decide, True, PUnit, or singleton substitution
is used.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2699TwoPlaceAssemblyActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual
open LeanFormal.IUT.XiFPaper.S2681HcompMinimalInputActual
open LeanFormal.IUT.XiFPaper.S2690TwoPlaceBadQActual
open LeanFormal.IUT.XiFPaper.S2696GaussianPlace2161Actual
open LeanFormal.IUT.XiFPaper.S2699LogQ2161Actual

local instance s2699TwoPlaceGaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-- The canonical Gaussian place above 2161 used by the S2699 local-log bound. -/
abbrev place2161Two : NumberField.FinitePlace GaussianField :=
  S2696GaussianPlace

/-- An actual q-candidate at that place, chosen from the DVR uniformizer
(finitePlaceQCandidate_nonempty).  This is the concrete 2161-side candidate
used in the instantiated corollaries; the main theorems are stated for an
arbitrary candidate. -/
noncomputable def q2161Two : FinitePlaceQCandidate place2161Two :=
  Classical.choice (finitePlaceQCandidate_nonempty place2161Two)

/-- The actual two-place bad-q absolute log |log ||q_5||| + |log ||q_2161|||
over the Gaussian places above 5 and 2161.  The five-side candidate is the
actual S2690TwoPlaceBadQActual.q5; the 2161-side candidate is a parameter. -/
noncomputable def sourceBadQAbsLog_twoPlace
    (q2161 : FinitePlaceQCandidate place2161Two) : Real :=
  |Real.log ‖q5.q‖| + |Real.log ‖q2161.q‖|

theorem sourceBadQAbsLog_twoPlace_def
    (q2161 : FinitePlaceQCandidate place2161Two) :
    sourceBadQAbsLog_twoPlace q2161 =
      |Real.log ‖q5.q‖| + |Real.log ‖q2161.q‖| := rfl

/-- The actual two-place bad-q quantity dominates log 5 + log 2161. -/
theorem log5_add_log2161_le
    (q2161 : FinitePlaceQCandidate place2161Two) :
    Real.log 5 + Real.log 2161 ≤ sourceBadQAbsLog_twoPlace q2161 := by
  unfold sourceBadQAbsLog_twoPlace
  linarith [q5_abs_log_ge_log5, S2699_log2161_le_abs_log_q q2161]

/-- Since log 5 < log 2161, the actual two-place quantity is strictly
greater than 2 * log 5. -/
theorem two_log5_lt
    (q2161 : FinitePlaceQCandidate place2161Two) :
    2 * Real.log 5 < sourceBadQAbsLog_twoPlace q2161 := by
  have hlt : Real.log (5 : ℝ) < Real.log (2161 : ℝ) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  linarith [log5_add_log2161_le q2161]

/-- Conditional hcomp reduction with an explicit numeric residual.  Given the
actual two-place/native bridge halign and the numeric residual
2 * log 5 <= sourceBadQAbsLog_twoPlace q2161, obtain exactly
S2681HcompMinimalInputActual.HcompBadQData T. -/
theorem hcomp_of_sourceBadQAbsLog_twoPlace
    {l : PrimeGeFive} {T : SourceNativeInitialThetaData.{0} l}
    [Fintype (Bad (nativePlaceSelection T))]
    (q2161 : FinitePlaceQCandidate place2161Two)
    (halign : sourceBadQAbsLog_twoPlace q2161 ≤ baseQTotalLogMagnitude T)
    (h : 2 * Real.log 5 ≤ sourceBadQAbsLog_twoPlace q2161) :
    HcompBadQData T := by
  unfold HcompBadQData
  linarith

/-- The same conditional hcomp reduction with the numeric residual discharged
by the proved strict inequality two_log5_lt.  The only remaining hypothesis
is the actual bridge to the native base-q total magnitude. -/
theorem hcompBadQData_of_sourceBadQAbsLog_twoPlace
    {l : PrimeGeFive} {T : SourceNativeInitialThetaData.{0} l}
    [Fintype (Bad (nativePlaceSelection T))]
    (q2161 : FinitePlaceQCandidate place2161Two)
    (halign : sourceBadQAbsLog_twoPlace q2161 ≤ baseQTotalLogMagnitude T) :
    HcompBadQData T :=
  hcomp_of_sourceBadQAbsLog_twoPlace q2161 halign
    (le_of_lt (two_log5_lt q2161))

/-- The concrete two-place quantity at the chosen 2161-side candidate. -/
theorem log5_add_log2161_le_q2161Two :
    Real.log 5 + Real.log 2161 ≤ sourceBadQAbsLog_twoPlace q2161Two :=
  log5_add_log2161_le q2161Two

/-- The concrete strict lower bound at the chosen 2161-side candidate. -/
theorem two_log5_lt_q2161Two :
    2 * Real.log 5 < sourceBadQAbsLog_twoPlace q2161Two :=
  two_log5_lt q2161Two

/-- Conditional hcomp at the chosen 2161-side candidate. -/
theorem hcompBadQData_of_sourceBadQAbsLog_twoPlace_concrete
    {l : PrimeGeFive} {T : SourceNativeInitialThetaData.{0} l}
    [Fintype (Bad (nativePlaceSelection T))]
    (halign : sourceBadQAbsLog_twoPlace q2161Two ≤ baseQTotalLogMagnitude T) :
    HcompBadQData T :=
  hcompBadQData_of_sourceBadQAbsLog_twoPlace q2161Two halign

/- Axiom audit. -/
#print axioms sourceBadQAbsLog_twoPlace_def
#print axioms log5_add_log2161_le
#print axioms two_log5_lt
#print axioms hcomp_of_sourceBadQAbsLog_twoPlace
#print axioms hcompBadQData_of_sourceBadQAbsLog_twoPlace
#print axioms log5_add_log2161_le_q2161Two
#print axioms two_log5_lt_q2161Two
#print axioms hcompBadQData_of_sourceBadQAbsLog_twoPlace_concrete

end LeanFormal.IUT.XiFPaper.S2699TwoPlaceAssemblyActual
end
