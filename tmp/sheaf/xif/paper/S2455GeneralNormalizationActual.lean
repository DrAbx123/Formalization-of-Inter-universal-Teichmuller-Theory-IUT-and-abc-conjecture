import tmp.sheaf.xif.paper.S2441C9PaperCarrierActual
import tmp.sheaf.xif.paper.S2450GeneralNormalizationActual

/-!
# S2455: general paper normalization from the actual q_v bad family

This file isolates the general candidate

  `S2455GeneralPaperNormalized S = -(sourceBadQAbsLog S) / (4 * (l.value : ℝ))`

and proves that it is an actual function of the bad q-parameter family, not a
paper-side assumption.

## What is actual here

* `sourceBadQAbsLog S` is the sum of `|Real.log (S.reduction.qParameter b)|`
  over the actual `SourceDefinition31Data.badPlaces`, using the actual
  `S.bad_finite` instance and the actual Definition 3.1(b)(c) q-parameter
  family `S.reduction.qParameter` (S1968's `paperQV` on the S1895 input).
* `S2455GeneralPaperNormalized S` is therefore the actual bad-q absolute-log
  sum divided by `4l`; no paper normalization, place, weight, procession, or
  other paper assumption occurs in its definition.
* On the concrete S1895 input, S2441's actual normalization
  `s2441_concrete_normalization` computes the source scalar as
  `-(order_C3 * log 5)`, so the general candidate is `-(order_C3 * log 5)/(4l)`,
  which is exactly S2450's `paperNormalizedSignedLog D`.

## What is proved

1. `S2455GeneralPaperNormalized_eq_sum`: the candidate is exactly
   `-(∑_b |log q_b|)/(4l)` over the actual bad places.
2. `S2455GeneralPaperNormalized_is_actual_qv_function`: the same equality,
   stated as the no-paper-assumption determination theorem; its right-hand
   side mentions only `S.reduction.qParameter`, `S.badPlaces`, and `l.value`.
3. `S2455GeneralPaperNormalized_paperInput`: for every
   `D : S1895PaperInput`, the candidate equals
   `LeanFormal.IUT.XiFPaper.S2450GeneralNormalizationActual.paperNormalizedSignedLog D`, using the
   S1968/S2441 concrete normalization.

## The exact missing structure

`S2455GeneralNormalizationRequired S` records the actual paper-normalized
scalar together with the place, weight, and procession data and the
identification `candidate_eq` with `S2455GeneralPaperNormalized S`.  No
inhabitant is constructed or asserted.  On the concrete S1895 input the
identification is proved by the theorem above, but the general paper-side
place/weight/procession package is not constructed in the tree.  The structure
is an interface record, not a proof that no inhabitant exists (compare S2451's
`S2451ProcessionAverageRequired`).

No `sorry`, `admit`, axiom, `True`/`PUnit` slot, arbitrary inhabitant, or
assumption-only gate is used.  This file was written under the serial
no-compile policy: it has not been compiled and no axiom probe was run.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

open scoped BigOperators

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.XiFPaper.S1960QPilotAnchorActual
open LeanFormal.IUT.XiFPaper.S2441C9PaperCarrierActual
open LeanFormal.IUT.XiFPaper.S2450GeneralNormalizationActual
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual

universe u

open LeanFormal.IUT

local instance s2455GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance s2455FivePrime : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

namespace LeanFormal.IUT.XiFPaper.S2455GeneralNormalizationActual

/-! ## 1. The actual bad q-v absolute-log sum and the general candidate -/

/-- The general candidate for the paper-normalized signed q-pilot log-volume,
computed from the actual bad q_v family.  This is the corrected `(4l)⁻¹` form:
the raw source sum `sourceBadQAbsLog S` is divided by `4l`, not used directly
as the paper scalar. -/
noncomputable def S2455GeneralPaperNormalized {l : PrimeGeFive}
    (S : SourceDefinition31Data.{u} l) : ℝ :=
  -(sourceBadQAbsLog S) / (4 * (l.value : ℝ))

/-- The candidate is exactly the negative total absolute log of the actual
`qParameter` family, divided by `4l`.  The `letI` exposes the actual
`S.bad_finite` instance used by `sourceBadQAbsLog`; no paper datum occurs. -/
theorem S2455GeneralPaperNormalized_eq_sum {l : PrimeGeFive}
    (S : SourceDefinition31Data.{u} l) :
    S2455GeneralPaperNormalized S =
      (-(letI := S.bad_finite;
         ∑ b : S.badPlaces, |Real.log (S.reduction.qParameter b)|)) /
        (4 * (l.value : ℝ)) := by
  unfold S2455GeneralPaperNormalized sourceBadQAbsLog
  rfl

/-- **The candidate is an actual function of the q_v data.**  The right-hand
side mentions only the actual `qParameter` family, the actual bad index, and
`l.value`; in particular no paper normalization, procession average, place or
weight choice is assumed.  This is the formal no-paper-assumption statement for
`S2455GeneralPaperNormalized`. -/
theorem S2455GeneralPaperNormalized_is_actual_qv_function {l : PrimeGeFive}
    (S : SourceDefinition31Data.{u} l) :
    S2455GeneralPaperNormalized S =
      (-(letI := S.bad_finite;
         ∑ b : S.badPlaces, |Real.log (S.reduction.qParameter b)|)) /
        (4 * (l.value : ℝ)) :=
  S2455GeneralPaperNormalized_eq_sum S

/-! ## 2. The concrete S1895 specialization -/

/-- The concrete S1895/S1968 bad q-parameter absolute-log sum is
`order_C3 * log 5`, obtained from S2441's concrete normalization theorem. -/
theorem S2455_sourceBadQAbsLog_paperInput (D : S1895PaperInput) :
    sourceBadQAbsLog (paperInput D).initial =
      (S1487Cand.order : ℝ) * Real.log 5 := by
  have h := s2441_concrete_normalization D
  unfold sourceQPilotSignedLog at h
  have h' := congrArg Neg.neg h
  simpa using h'

/-- The general candidate specializes to S2450's paper-normalized scalar on the
concrete S1895 input.  This uses S1968's actual bad-q computation through
S2441's `s2441_concrete_normalization` and S2450's
`paperNormalizedSignedLog_eq`. -/
theorem S2455GeneralPaperNormalized_paperInput (D : S1895PaperInput) :
    S2455GeneralPaperNormalized (paperInput D).initial =
      LeanFormal.IUT.XiFPaper.S2450GeneralNormalizationActual.paperNormalizedSignedLog D := by
  unfold S2455GeneralPaperNormalized
  rw [S2455_sourceBadQAbsLog_paperInput D,
    LeanFormal.IUT.XiFPaper.S2450GeneralNormalizationActual.paperNormalizedSignedLog_eq D]
  rw [neg_div]

/-! ## 3. The exact missing general paper normalization -/

/-- The actual finite weighted sum over the bad q_v family, using the actual
`S.bad_finite` instance.  This is the bad-place sum appearing in the paper
normalization formula. -/
noncomputable def S2455WeightedBadSum {l : PrimeGeFive}
    (S : SourceDefinition31Data.{u} l) (weight : S.badPlaces → ℝ) : ℝ :=
  letI := S.bad_finite
  ∑ b : S.badPlaces, weight b

/-- The weighted bad sum is the literal finite sum over the actual bad
places. -/
theorem S2455WeightedBadSum_eq_sum {l : PrimeGeFive}
    (S : SourceDefinition31Data.{u} l) (weight : S.badPlaces → ℝ) :
    S2455WeightedBadSum S weight =
      (letI := S.bad_finite;
       ∑ b : S.badPlaces, weight b) := by
  unfold S2455WeightedBadSum
  rfl

/-- **The exact missing general paper normalization.**

`paperNormalized` is the paper's normalized signed scalar `-|log q|` for the
source datum `S`.  The fields `place`, `weight`, and `procession` are the
actual paper-side data: the bad place selected by each q-parameter, the local
absolute-log q-weight, and the Proposition 3.9(i) procession normalization
factor.  The paper formula has the IUT-IV root factor `(2l)⁻¹` and the global
degree normalization `1/[F:Q]`, displayed as the denominator
`2 * l.value * Module.finrank ℚ S.arithmetic.Fmod`; the weight `S`-sum is
`∑_b weight_b`.  `candidate_eq` is the missing identification of this paper
scalar with the actual q_v candidate `S2455GeneralPaperNormalized S`.

No inhabitant is constructed or asserted.  This is an interface record, not a
proof that no inhabitant exists: on the concrete S1895 input the candidate is
proved to equal S2450's paper-normalized scalar, but the general place, weight,
and procession package is not constructed in the tree.  The formula in
`paperNormalized_eq` is itself part of the missing interface, not a proved
theorem of this file. -/
structure S2455GeneralNormalizationRequired {l : PrimeGeFive}
    (S : SourceDefinition31Data.{u} l) where
  /-- the actual bad place selected by each bad q-parameter -/
  place : S.badPlaces → S.selectedPlaces
  /-- it is the actual Definition 3.1(b) bad inclusion -/
  place_eq : ∀ b, place b = S.reduction.partition.badIncluded b
  /-- the actual local absolute-log q-weight at each bad place -/
  weight : S.badPlaces → ℝ
  /-- it is the actual `|log q_b|` -/
  weight_eq : ∀ b, weight b = |Real.log (S.reduction.qParameter b)|
  /-- the actual Proposition 3.9(i) procession normalization factor -/
  procession : ℝ
  /-- the actual paper normalized signed scalar `-|log q|` -/
  paperNormalized : ℝ
  /-- the paper formula: root factor `(2l)⁻¹`, global normalization
  `1/[F:Q]`, the bad-place weight sum, and the procession factor -/
  paperNormalized_eq :
    paperNormalized =
      (-(procession * S2455WeightedBadSum S weight)) /
        (2 * (l.value : ℝ) *
          (Module.finrank ℚ (S.arithmetic.Fmod) : ℝ))
  /-- **the missing identification**: the actual q_v candidate is the paper
  normalized scalar -/
  candidate_eq : S2455GeneralPaperNormalized S = paperNormalized

/-- Any inhabitant of the exact missing structure has its `paperNormalized`
field equal to the actual q_v candidate.  This is only a conditional
consequence of `candidate_eq`; it is not an inhabitant of the structure. -/
theorem S2455GeneralNormalizationRequired_paperNormalized_eq
    {l : PrimeGeFive} {S : SourceDefinition31Data.{u} l}
    (h : S2455GeneralNormalizationRequired S) :
    h.paperNormalized = S2455GeneralPaperNormalized S :=
  h.candidate_eq.symm

/-- Conditional concrete consequence: if the exact missing general structure
were inhabited on the S1895 input, its paper scalar would be S2450's
paper-normalized scalar.  No inhabitant is constructed or asserted. -/
theorem S2455GeneralNormalizationRequired_paperNormalized_eq_s2450
    (D : S1895PaperInput)
    (h : S2455GeneralNormalizationRequired (paperInput D).initial) :
    h.paperNormalized =
      LeanFormal.IUT.XiFPaper.S2450GeneralNormalizationActual.paperNormalizedSignedLog D := by
  calc
    h.paperNormalized = S2455GeneralPaperNormalized (paperInput D).initial :=
      S2455GeneralNormalizationRequired_paperNormalized_eq
        (S := (paperInput D).initial) h
    _ = LeanFormal.IUT.XiFPaper.S2450GeneralNormalizationActual.paperNormalizedSignedLog D :=
      S2455GeneralPaperNormalized_paperInput D

/-! ## 4. Interface checks (not run in this file; serial no-compile policy) -/

#check S2455GeneralPaperNormalized
#check S2455GeneralPaperNormalized_eq_sum
#check S2455GeneralPaperNormalized_is_actual_qv_function
#check S2455_sourceBadQAbsLog_paperInput
#check S2455GeneralPaperNormalized_paperInput
#check S2455WeightedBadSum
#check S2455WeightedBadSum_eq_sum
#check S2455GeneralNormalizationRequired
#check S2455GeneralNormalizationRequired_paperNormalized_eq
#check S2455GeneralNormalizationRequired_paperNormalized_eq_s2450

end LeanFormal.IUT.XiFPaper.S2455GeneralNormalizationActual
end
