import tmp.sheaf.xif.paper.S2689Place2161Actual
import tmp.sheaf.xif.paper.S1487OQPilotScalarEqualityActual
import tmp.sheaf.xif.paper.S2681HcompMinimalInputActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange

/-!
# S2690: the actual two-place Gaussian bad-q absolute log (5 and 2161)

Layer: source q-side (sourceBadQAbsLog) on the actual Gaussian field
GaussianField = Q(i).  Consumer: the hcomp bad-q data
S2681HcompMinimalInputActual.HcompBadQData (numerically the same proposition
as S2678PaperUnconditionalHcompActual.NativeResidual).

## Actual objects used

* concreteGaussianFivePlace : NumberField.FinitePlace GaussianField, the
  concrete Gaussian place above 5, with
  residueNormBase concreteGaussianFivePlace = 5
  (S1487OQPilotScalarEqualityActual.S1487_residueNormBase_five, from the
  actual residue field ZMod 5).
* S2689Place2161Actual.S2689GaussianPlace2161, a Gaussian place above the
  rational prime 2161, with
  comap S2689GaussianPlace2161 = rationalFinitePlace 2161
  (S2689GaussianPlace2161_comap).
* the actual q-candidates are Classical.choice of
  NumberFieldFinitePlace.finitePlaceQCandidate_nonempty at these two places.
  They are candidate choices: no order is pinned, and no Tate uniformization
  is asserted.  The bounds below depend only on the candidate law
  (order >= 1) and on the actual residue norm bases, so any candidate works.

## The quantity

sourceBadQAbsLog_actual = |log ||q_5||| + |log ||q_2161||| is the per-place
bad-q absolute log over the two actual Gaussian places.  Here log q is the
logarithm of the actual completion norm ||q|| (the notation of the paper's
|log q_b|); this is exactly Mathlib's localSignedLog.

## What is proved

* q5_abs_log_ge_log5 : log 5 <= |log ||q_5|||.
* q2161_abs_log_ge_log2161 : log 2161 <= |log ||q_2161|||, from
  residueNormBase = 2161 ^ f with f = localResidueDegree >= 1
  (residueNormBase_2161_ge).  The exact value 2161 would additionally need
  f = 1, i.e. that the chosen place has residue degree one over 2161; only
  the lower bound is used, and it is proved.
* sourceBadQAbsLog_actual_ge : log 5 + log 2161 <= sourceBadQAbsLog_actual.
* two_log5_lt : 2 * log 5 < sourceBadQAbsLog_actual since log 5 < log 2161.
* the conditional hcomp reduction hcomp_of_sourceBadQAbsLogActual, which from
  the explicit numeric residual on the two-place actual quantity and the
  actual bridge sourceBadQAbsLog_actual <= baseQTotalLogMagnitude T produces
  exactly S2681HcompMinimalInputActual.HcompBadQData T, the residual consumed
  by S2681/S2678.  The bridge (identifying the two Gaussian local logs with
  the native base-q total magnitude) is the missing actual alignment and is
  kept as an explicit hypothesis; it is not asserted or faked.  Its
  unconditional corollary hcompBadQData_of_sourceBadQAbsLogActual uses
  two_log5_lt to discharge the numeric residual.

No sorry, admit, axiom, native_decide, True, PUnit, or singleton substitution
is used.  The S1280 singleton selection is not touched here: the two-place
quantity is built directly on the actual Gaussian field.
-/

noncomputable section
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2690TwoPlaceBadQActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual
open LeanFormal.IUT.XiFPaper.S2689Place2161Actual
open LeanFormal.IUT.XiFPaper.S2681HcompMinimalInputActual
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual

local instance s2690GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance s2690FivePrime : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
local instance s2690_2161Prime : Fact (Nat.Prime 2161) := ⟨by norm_num⟩

universe u uX uLabel

/-! ## 1. The two actual places and their q-candidate choices -/

/-- The Gaussian place above 5: the concrete place used by the O-layer scalar
comparison. -/
abbrev placeFive : NumberField.FinitePlace GaussianField :=
  concreteGaussianFivePlace

/-- The Gaussian place above 2161 supplied by S2689. -/
abbrev place2161 : NumberField.FinitePlace GaussianField :=
  S2689GaussianPlace2161

/-- The actual q-candidate at the Gaussian five place, chosen classically from
the DVR uniformizer (no order is pinned). -/
noncomputable def q5 : FinitePlaceQCandidate placeFive :=
  Classical.choice (finitePlaceQCandidate_nonempty placeFive)

/-- The actual q-candidate at the Gaussian place above 2161, chosen classically
from the DVR uniformizer (no order is pinned). -/
noncomputable def q2161 : FinitePlaceQCandidate place2161 :=
  Classical.choice (finitePlaceQCandidate_nonempty place2161)

/-! ## 2. The two-place actual bad-q absolute log -/

/-- The actual two-place bad-q absolute log: |log q_5| + |log q_2161|, where
log q is the logarithm of the actual completion norm ||q||. -/
noncomputable def sourceBadQAbsLog_actual : Real :=
  |Real.log ‖q5.q‖| + |Real.log ‖q2161.q‖|

theorem sourceBadQAbsLog_actual_def :
    sourceBadQAbsLog_actual = |Real.log ‖q5.q‖| + |Real.log ‖q2161.q‖| := rfl

/-- Each summand is the corresponding local log-magnitude. -/
theorem abs_log_norm_q5 :
    |Real.log ‖q5.q‖| = localLogMagnitude q5 := by
  have h : |localSignedLog q5| = localLogMagnitude q5 := abs_localSignedLog q5
  simpa only [localSignedLog] using h

theorem abs_log_norm_q2161 :
    |Real.log ‖q2161.q‖| = localLogMagnitude q2161 := by
  have h : |localSignedLog q2161| = localLogMagnitude q2161 :=
    abs_localSignedLog q2161
  simpa only [localSignedLog] using h

/-- The two-place quantity is the sum of the two actual local log-magnitudes. -/
theorem sourceBadQAbsLog_actual_eq_localLogMagnitude_add :
    sourceBadQAbsLog_actual = localLogMagnitude q5 + localLogMagnitude q2161 := by
  rw [sourceBadQAbsLog_actual, abs_log_norm_q5, abs_log_norm_q2161]

theorem sourceBadQAbsLog_actual_pos : 0 < sourceBadQAbsLog_actual := by
  rw [sourceBadQAbsLog_actual_eq_localLogMagnitude_add]
  exact add_pos (localLogMagnitude_pos q5) (localLogMagnitude_pos q2161)

/-! ## 3. Residue norm bases of the two actual places -/

/-- The residue norm base of the concrete Gaussian five place is 5. -/
theorem residueNormBase_five : residueNormBase placeFive = 5 :=
  S1487_residueNormBase_five

/-- The absolute norm of the maximal ideal of the rational finite place at p is
p: the quotient is Z (mod p), whose cardinality is p. -/
theorem absNorm_rationalFinitePlace (p : Nat) [Fact (Nat.Prime p)] :
    Ideal.absNorm (rationalFinitePlace p).maximalIdeal.asIdeal = p := by
  have hgen : Rat.HeightOneSpectrum.natGenerator (rationalHeightOneSpectrum p) = p := by
    have h := (Rat.HeightOneSpectrum.primesEquiv
      (R := NumberField.RingOfIntegers ℚ)).apply_symm_apply ⟨p, Fact.out⟩
    exact congrArg (fun q : Nat.Primes => q.1) h
  have hspan := Rat.HeightOneSpectrum.span_natGenerator (rationalHeightOneSpectrum p)
  rw [hgen] at hspan
  have hcard :
      Nat.card (NumberField.RingOfIntegers ℚ ⧸
        (rationalHeightOneSpectrum p).asIdeal) = p := by
    rw [Nat.card_congr (Ideal.quotientEquiv (rationalHeightOneSpectrum p).asIdeal
      (Ideal.span {(p : Int)})
      (Rat.IsIntegralClosure.intEquiv (NumberField.RingOfIntegers ℚ))
      hspan).toEquiv]
    exact Int.card_ideal_quot p
  unfold rationalFinitePlace
  rw [NumberField.FinitePlace.maximalIdeal_mk, Ideal.absNorm_apply,
    Submodule.cardQuot_apply, hcard]

/-- The residue norm base of the rational finite place at 2161 is 2161. -/
theorem residueNormBase_rationalFinitePlace_2161 :
    residueNormBase (rationalFinitePlace 2161) = 2161 := by
  rw [residueNormBase]
  rw [absNorm_rationalFinitePlace]
  norm_num

/-- The residue norm base at the S2689 Gaussian place above 2161 is 2161 ^ f
where f = localResidueDegree >= 1 is the residue degree. -/
theorem residueNormBase_2161_eq_pow :
    residueNormBase place2161 =
      2161 ^ localResidueDegree (k := ℚ) place2161 := by
  have hpow := residueNormBase_eq_lower_pow (k := ℚ) place2161
  rw [S2689GaussianPlace2161_comap, residueNormBase_rationalFinitePlace_2161] at hpow
  exact hpow

/-- Consequently the residue norm base at the place above 2161 is at least
2161.  (Exact equality would require residue degree one; not needed here.) -/
theorem residueNormBase_2161_ge :
    (2161 : Real) ≤ residueNormBase place2161 := by
  rw [residueNormBase_2161_eq_pow]
  have hf : 0 < localResidueDegree (k := ℚ) place2161 :=
    localResidueDegree_pos (k := ℚ) place2161
  calc (2161 : Real) = (2161 : Real) ^ 1 := (pow_one 2161).symm
    _ ≤ (2161 : Real) ^ localResidueDegree (k := ℚ) place2161 :=
        pow_le_pow_right₀ (by norm_num) (Nat.one_le_iff_ne_zero.mpr hf.ne')

/-! ## 4. The per-place lower bounds -/

/-- At the Gaussian five place, log 5 <= |log q_5|. -/
theorem q5_abs_log_ge_log5 :
    Real.log 5 ≤ |Real.log ‖q5.q‖| := by
  rw [abs_log_norm_q5, localLogMagnitude_eq_order_mul_log, residueNormBase_five]
  have hlog : 0 < Real.log (5 : Real) := Real.log_pos (by norm_num)
  have horder : (1 : Real) ≤ (q5.order : Real) := by
    exact_mod_cast q5.order_pos
  calc Real.log 5 = 1 * Real.log 5 := (one_mul _).symm
    _ ≤ (q5.order : Real) * Real.log 5 :=
        mul_le_mul_of_nonneg_right horder (le_of_lt hlog)

/-- At the Gaussian place above 2161, log 2161 <= |log q_2161|. -/
theorem q2161_abs_log_ge_log2161 :
    Real.log 2161 ≤ |Real.log ‖q2161.q‖| := by
  rw [abs_log_norm_q2161, localLogMagnitude_eq_order_mul_log]
  have hlog : Real.log (2161 : Real) ≤ Real.log (residueNormBase place2161) :=
    Real.log_le_log (by norm_num) residueNormBase_2161_ge
  have hpos : 0 < Real.log (residueNormBase place2161) :=
    log_residueNormBase_pos place2161
  have horder : (1 : Real) ≤ (q2161.order : Real) := by
    exact_mod_cast q2161.order_pos
  calc Real.log 2161 ≤ Real.log (residueNormBase place2161) := hlog
    _ = 1 * Real.log (residueNormBase place2161) := (one_mul _).symm
    _ ≤ (q2161.order : Real) * Real.log (residueNormBase place2161) :=
        mul_le_mul_of_nonneg_right horder (le_of_lt hpos)

/-! ## 5. The two-place lower bound and strictness -/

/-- The actual two-place bad-q absolute log dominates log 5 + log 2161. -/
theorem sourceBadQAbsLog_actual_ge :
    Real.log 5 + Real.log 2161 ≤ sourceBadQAbsLog_actual := by
  rw [sourceBadQAbsLog_actual]
  linarith [q5_abs_log_ge_log5, q2161_abs_log_ge_log2161]

/-- Since log 5 < log 2161, the actual quantity is strictly greater than
2 log 5. -/
theorem two_log5_lt :
    2 * Real.log 5 < sourceBadQAbsLog_actual := by
  have hlt : Real.log (5 : Real) < Real.log (2161 : Real) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  linarith [sourceBadQAbsLog_actual_ge]

/-! ## 6. Conditional connection to the hcomp bad-q data -/

/-- Conditional hcomp reduction.  Given the actual bridge identifying the
two-place Gaussian bad-q total with the native base-q total magnitude, the
numeric residual 2 log 5 <= sourceBadQAbsLog_actual gives exactly
S2681HcompMinimalInputActual.HcompBadQData T
(2 log 5 <= baseQTotalLogMagnitude T), the bad-q data consumed by S2681
(hcomp_of_agreement_badQ, hcomp_of_minimalInput) and identical to S2678's
NativeResidual.  The bridge is the genuine missing alignment and is an
explicit hypothesis here. -/
theorem hcomp_of_sourceBadQAbsLogActual
    {l : PrimeGeFive} {T : SourceNativeInitialThetaData.{0} l}
    [Fintype (Bad (nativePlaceSelection T))]
    (halign : sourceBadQAbsLog_actual ≤ baseQTotalLogMagnitude T)
    (h : 2 * Real.log 5 ≤ sourceBadQAbsLog_actual) :
    S2681HcompMinimalInputActual.HcompBadQData T := by
  unfold S2681HcompMinimalInputActual.HcompBadQData
  linarith

/-- The same reduction with the numeric residual discharged by the proved
strict inequality two_log5_lt.  The only hypothesis left is the actual bad-q
alignment with the native total magnitude. -/
theorem hcompBadQData_of_sourceBadQAbsLogActual
    {l : PrimeGeFive} {T : SourceNativeInitialThetaData.{0} l}
    [Fintype (Bad (nativePlaceSelection T))]
    (halign : sourceBadQAbsLog_actual ≤ baseQTotalLogMagnitude T) :
    S2681HcompMinimalInputActual.HcompBadQData T :=
  hcomp_of_sourceBadQAbsLogActual halign (le_of_lt two_log5_lt)

/-! ## 7. Axiom audit -/

#print axioms q5_abs_log_ge_log5
#print axioms q2161_abs_log_ge_log2161
#print axioms sourceBadQAbsLog_actual_ge
#print axioms two_log5_lt
#print axioms hcomp_of_sourceBadQAbsLogActual
#print axioms hcompBadQData_of_sourceBadQAbsLogActual

end LeanFormal.IUT.XiFPaper.S2690TwoPlaceBadQActual
end
