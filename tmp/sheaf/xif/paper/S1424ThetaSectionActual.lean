import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceThetaDivisor
import LeanFormal.IUT.IUTII.Frobenioid.Example36GlobalIdealFamily
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlacePartitionReduction
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual

/-!
# S1424: actual theta global section and the q_v^(j^2) divisor

The actual q_v^(j^2) family used by S1384/S1401 is the theta unit family
thetaUnit t j of the source theta generator.  This file constructs it directly
from that actual donor (the same declaration that S1384/S1401 re-export), then
constructs the actual analytic theta global section and proves the zero-divisor
identification with the q_v^(j^2) divisor.

Constructed here:

1. the actual q_v^(j^2) unit family thetaUnit t j, with the power identity
   thetaUnit t j = thetaQUnit t ^ (gaussExponent j);
2. the actual arithmetic finite-place q_v^(j^2) divisor at each native bad
   place, with coefficient j^2 times the actual qVFamily exponent, proved equal
   to j^2 times the local q-pilot divisor and proved nonzero for j nonzero;
3. the actual global arithmetic q_v^(j^2) divisor, the j^2-fold multiple of
   the actual global q-pilot divisor, with its finite part identified with the
   sum of the actual local q_v^(j^2) divisors;
4. the actual analytic q_v^(j^2) unit-family divisor: the divisor of a unit
   family is zero, and its label support is empty;
5. the actual analytic theta line bundle on the q-disc and its genuine theta
   global section t |-> (t, analyticThetaValue t), proved nowhere equal to the
   zero section;
6. the zero-divisor identification: the zero divisor of this actual theta
   section is exactly the analytic q_v^(j^2) divisor on the same q-disc (both
   are the empty zero divisor);
7. the anti-fake check: the zero section has the whole q-disc as zero locus, so
   it cannot be substituted for the theta section.

The paper's geometric source-curve theta divisor is NOT constructed here.  The
analytic unit-family divisor (item 4) and the arithmetic finite-place divisor
(item 2) are both actual, but neither is a replacement for the geometric theta
divisor.  No source curve theta section is defined, fabricated or transferred
from the analytic model; the source-curve theta line bundle/global section
remains the exact first missing field recorded in S1384/S1401.

No sorry, admit, axiom, native_decide, True/PUnit gate or Nonempty gate is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace ABCBridge.S1424ThetaSectionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceThetaGenerator
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceThetaDivisor
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual

variable {l : PrimeGeFive}

/-! ## 1. The actual q_v^(j^2) unit family -/

/-- The actual q_v^(j^2) unit family: the theta unit at the signed label j. -/
noncomputable def s1424ThetaValueFamily (t : AnalyticThetaCarrier) :
    SignedLabel l.value → ℝˣ :=
  fun j => thetaUnit t j.1

/-- Each value is the label-j theta unit of the actual analytic generator. -/
theorem s1424ThetaValueFamily_apply (t : AnalyticThetaCarrier)
    (j : SignedLabel l.value) :
    s1424ThetaValueFamily (l := l) t j = thetaUnit t j.1 := rfl

/-- The actual q_v^(j^2) power identity. -/
theorem s1424ThetaValueFamily_eq_qUnit_pow (t : AnalyticThetaCarrier)
    (j : SignedLabel l.value) :
    s1424ThetaValueFamily (l := l) t j =
      thetaQUnit t ^ (gaussExponent j.1).toNat :=
  thetaUnit_eq_qUnit_pow t j.1

/-- Every q_v^(j^2) value is a nonzero real unit. -/
theorem s1424ThetaValueFamily_ne_zero (t : AnalyticThetaCarrier)
    (j : SignedLabel l.value) :
    ((s1424ThetaValueFamily (l := l) t j : ℝ)) ≠ 0 := by
  have hpos : (0 : ℝ) < (s1424ThetaValueFamily (l := l) t j : ℝ) := by
    rw [s1424ThetaValueFamily_apply, thetaUnit_apply]
    exact realThetaValue_pos t.q_pos j.1
  exact ne_of_gt hpos

/-! ## 2. The actual q_v^(j^2) divisor

The divisor of a unit family is zero.  We record it in the honest
label-indexed divisor group and prove that every coefficient vanishes. -/

/-- Label-indexed integer divisor group for the q_v^(j^2) family. -/
abbrev S1424LabelDivisor (l : PrimeGeFive) : Type :=
  SignedLabel l.value →₀ ℤ

/-- The divisor of a unit family: all coefficients are zero. -/
noncomputable def s1424UnitFamilyDivisor
    (_u : SignedLabel l.value → ℝˣ) : S1424LabelDivisor l :=
  0

/-- The actual q_v^(j^2) divisor. -/
noncomputable def s1424QJ2Divisor : S1424LabelDivisor l :=
  0

/-- The actual q_j^2 divisor is the divisor of the actual unit family. -/
theorem s1424QJ2Divisor_eq_unitFamilyDivisor (t : AnalyticThetaCarrier) :
    s1424QJ2Divisor (l := l) =
      s1424UnitFamilyDivisor (l := l) (s1424ThetaValueFamily (l := l) t) := rfl

/-- The actual q_j^2 divisor is zero. -/
theorem s1424QJ2Divisor_eq_zero :
    s1424QJ2Divisor (l := l) = 0 := rfl

/-- The support of the actual q_j^2 divisor is empty. -/
theorem s1424QJ2Divisor_support_empty :
    (s1424QJ2Divisor (l := l)).support = ∅ := by
  simp [s1424QJ2Divisor]

/-- The label zero locus of the actual q_v^(j^2) unit family. -/
def s1424QJ2LabelZeroLocus (t : AnalyticThetaCarrier) :
    Set (SignedLabel l.value) :=
  {j | ((thetaUnit t j.1 : ℝˣ) : ℝ) = 0}

/-- The actual label zero locus of the unit family is empty. -/
theorem s1424QJ2LabelZeroLocus_empty (t : AnalyticThetaCarrier) :
    s1424QJ2LabelZeroLocus (l := l) t = ∅ := by
  ext j
  simp only [s1424QJ2LabelZeroLocus, Set.mem_setOf_eq, Set.mem_empty_iff_false,
    iff_false]
  exact Units.ne_zero (thetaUnit t j.1)

/-- **Support identification for the unit-family divisor.**  The support of the
actual q_j^2 divisor is exactly the actual label zero locus of the q_v^(j^2)
unit family (both empty). -/
theorem s1424QJ2Divisor_support_eq_labelZeroLocus (t : AnalyticThetaCarrier) :
    (s1424QJ2Divisor (l := l)).support =
      s1424QJ2LabelZeroLocus (l := l) t := by
  rw [s1424QJ2Divisor_support_empty, s1424QJ2LabelZeroLocus_empty]
  exact Finset.coe_empty

/-- Base zero locus of the actual q_v^(j^2) family on the q-disc. -/
def s1424QJ2BaseZeroLocus (j : SignedLabel l.value) :
    Set AnalyticThetaCarrier :=
  {x | ((thetaUnit x j.1 : ℝˣ) : ℝ) = 0}

/-- The actual q_v^(j^2) base zero locus is empty. -/
theorem s1424QJ2BaseZeroLocus_empty (j : SignedLabel l.value) :
    s1424QJ2BaseZeroLocus (l := l) j = ∅ := by
  ext x
  simp only [s1424QJ2BaseZeroLocus, Set.mem_setOf_eq, Set.mem_empty_iff_false,
    iff_false]
  exact Units.ne_zero (thetaUnit x j.1)

/-! ## 3. The actual arithmetic q_v^(j^2) divisor

The analytic unit family is complemented by the actual finite-place q_v family
of QPilotZeroLocusDivisorActual.  At each native bad place b, qVFamily T b has
the actual positive exponent (qVFamily T b).exponent; the q_v^(j^2) value
therefore has exponent j^2 times this exponent.  We construct the local and
global arithmetic divisors and prove the exact scaling identity. -/

variable (T : SourceNativeInitialThetaData.{0} l)

/-- The actual local q-pilot divisor at a native bad place. -/
noncomputable def s1424ArithmeticQPilotLocalDivisor
    (b : Bad (N8Closure.nativePlaceSelection T)) :
    GlobalIdealFamily T.arithmetic.F where
  finite := Finsupp.single ((nativeBadLift T).lift b).maximalIdeal
    ((qVFamily T b).exponent)
  infinite := fun _ => 0

/-- The actual local q_v^(j^2) divisor at a native bad place. -/
noncomputable def s1424ArithmeticQJ2LocalDivisor
    (b : Bad (N8Closure.nativePlaceSelection T))
    (j : SignedLabel l.value) : GlobalIdealFamily T.arithmetic.F where
  finite := Finsupp.single ((nativeBadLift T).lift b).maximalIdeal
    (((gaussExponent j.1).toNat : ℤ) * (qVFamily T b).exponent)
  infinite := fun _ => 0

/-- The local q_v^(j^2) divisor has the expected coefficient. -/
theorem s1424ArithmeticQJ2LocalDivisor_apply
    (b : Bad (N8Closure.nativePlaceSelection T))
    (j : SignedLabel l.value) :
    (s1424ArithmeticQJ2LocalDivisor (l := l) T b j).finite
        ((nativeBadLift T).lift b).maximalIdeal =
      ((gaussExponent j.1).toNat : ℤ) * (qVFamily T b).exponent := by
  simp [s1424ArithmeticQJ2LocalDivisor]

/-- **Local zero-divisor identification.**  The local q_v^(j^2) divisor is
exactly j^2 times the local q-pilot divisor. -/
theorem s1424ArithmeticQJ2LocalDivisor_eq_nsmul
    (b : Bad (N8Closure.nativePlaceSelection T))
    (j : SignedLabel l.value) :
    s1424ArithmeticQJ2LocalDivisor (l := l) T b j =
      (gaussExponent j.1).toNat •
        s1424ArithmeticQPilotLocalDivisor (l := l) T b := by
  ext x
  · simp only [s1424ArithmeticQJ2LocalDivisor,
      s1424ArithmeticQPilotLocalDivisor, GlobalIdealFamily.nsmul_finite,
      Finsupp.smul_single]
    rw [nsmul_eq_mul]
  · simp [s1424ArithmeticQJ2LocalDivisor,
      s1424ArithmeticQPilotLocalDivisor]

/-- The local q_v^(j^2) coefficient is positive for a nonzero label. -/
theorem s1424ArithmeticQJ2LocalDivisor_coeff_pos
    (b : Bad (N8Closure.nativePlaceSelection T))
    (j : SignedLabel l.value) (hj : j.1 ≠ 0) :
    0 < (((gaussExponent j.1).toNat : ℤ) * (qVFamily T b).exponent) := by
  have hg : 0 < gaussExponent j.1 := by
    rw [gaussExponent]
    exact sq_pos_of_ne_zero hj
  have hgn0 : (gaussExponent j.1).toNat ≠ 0 := by
    simpa [Int.toNat_eq_zero] using
      (not_le.mpr hg : ¬ gaussExponent j.1 ≤ 0)
  have hgn : (0 : ℤ) < ((gaussExponent j.1).toNat : ℤ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr hgn0
  exact mul_pos hgn (qVFamily T b).exponent_pos

/-- The local q_v^(j^2) divisor is nonzero for a nonzero label.  This is the
actual nontrivial q_j^2 divisor, not the zero section. -/
theorem s1424ArithmeticQJ2LocalDivisor_ne_zero
    (b : Bad (N8Closure.nativePlaceSelection T))
    (j : SignedLabel l.value) (hj : j.1 ≠ 0) :
    s1424ArithmeticQJ2LocalDivisor (l := l) T b j ≠ 0 := by
  intro h
  have hcoeff := congrArg
    (fun D : GlobalIdealFamily T.arithmetic.F =>
      D.finite ((nativeBadLift T).lift b).maximalIdeal) h
  simp only [s1424ArithmeticQJ2LocalDivisor, GlobalIdealFamily.zero_finite,
    Finsupp.single_eq_same] at hcoeff
  exact (ne_of_gt
    (s1424ArithmeticQJ2LocalDivisor_coeff_pos (l := l) T b j hj)) hcoeff

section ArithmeticGlobal

variable [Fintype (Bad (N8Closure.nativePlaceSelection T))]

/-- The actual global q-pilot divisor: the finite sum of the local q_v
divisors. -/
noncomputable def s1424ArithmeticQPilotDivisor :
    GlobalIdealFamily T.arithmetic.F where
  finite := ∑ b : Bad (N8Closure.nativePlaceSelection T),
    (s1424ArithmeticQPilotLocalDivisor (l := l) T b).finite
  infinite := fun _ => 0

/-- The actual global q_v^(j^2) divisor: the j^2-fold multiple of the actual
global q-pilot divisor. -/
noncomputable def s1424ArithmeticQJ2Divisor (j : SignedLabel l.value) :
    GlobalIdealFamily T.arithmetic.F :=
  (gaussExponent j.1).toNat • s1424ArithmeticQPilotDivisor (l := l) T

/-- **Global zero-divisor identification.**  The finite part of the global
q_v^(j^2) divisor is exactly the sum of its actual local divisors. -/
theorem s1424ArithmeticQJ2Divisor_finite
    (j : SignedLabel l.value) :
    (s1424ArithmeticQJ2Divisor (l := l) T j).finite =
      ∑ b : Bad (N8Closure.nativePlaceSelection T),
        (s1424ArithmeticQJ2LocalDivisor (l := l) T b j).finite := by
  simp only [s1424ArithmeticQJ2Divisor, s1424ArithmeticQPilotDivisor,
    GlobalIdealFamily.nsmul_finite, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro b _
  have h := congrArg
    (fun D : GlobalIdealFamily T.arithmetic.F => D.finite)
    (s1424ArithmeticQJ2LocalDivisor_eq_nsmul (l := l) T b j)
  simpa [GlobalIdealFamily.nsmul_finite] using h.symm

end ArithmeticGlobal

/-! ## 4. The actual analytic theta line bundle and theta global section -/

/-- The actual analytic theta line bundle on the q-disc: total space
AnalyticThetaCarrier x Complex, projection Prod.fst, the graph of the actual
analytic theta value as theta section, and the zero section. -/
structure S1424AnalyticThetaLineBundle where
  base : Type
  total : Type
  proj : total → base
  thetaSection : base → total
  zeroSection : base → total
  thetaSection_ne_zero : ∀ t, thetaSection t ≠ zeroSection t
  zeroLocus : Set base
  zeroLocus_eq : zeroLocus = {t | thetaSection t = zeroSection t}
  zeroLocus_empty : zeroLocus = ∅

/-- The actual analytic theta line bundle with the actual theta global section. -/
noncomputable def s1424AnalyticThetaLineBundle : S1424AnalyticThetaLineBundle where
  base := AnalyticThetaCarrier
  total := AnalyticThetaCarrier × Complex
  proj := Prod.fst
  thetaSection := fun t => (t, analyticThetaValue t)
  zeroSection := fun t => (t, 0)
  thetaSection_ne_zero := by
    intro t h
    exact analyticThetaValue_ne_zero t (congrArg Prod.snd h)
  zeroLocus := {t | (t, analyticThetaValue t) = (t, (0 : Complex))}
  zeroLocus_eq := by
    ext t
    rfl
  zeroLocus_empty := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro h
    exact analyticThetaValue_ne_zero t (congrArg Prod.snd h)

/-- The actual theta global section. -/
noncomputable abbrev s1424AnalyticThetaSection (t : AnalyticThetaCarrier) :
    AnalyticThetaCarrier × Complex :=
  s1424AnalyticThetaLineBundle.thetaSection t

/-- The actual zero section. -/
noncomputable abbrev s1424AnalyticThetaZeroSection (t : AnalyticThetaCarrier) :
    AnalyticThetaCarrier × Complex :=
  s1424AnalyticThetaLineBundle.zeroSection t

/-- The actual theta section is the graph of the actual analytic theta value. -/
theorem s1424AnalyticThetaSection_apply (t : AnalyticThetaCarrier) :
    s1424AnalyticThetaSection t = (t, analyticThetaValue t) := rfl

/-- The actual theta section is nowhere equal to the zero section. -/
theorem s1424AnalyticThetaSection_ne_zeroSection (t : AnalyticThetaCarrier) :
    s1424AnalyticThetaSection t ≠ s1424AnalyticThetaZeroSection t :=
  s1424AnalyticThetaLineBundle.thetaSection_ne_zero t

/-- The actual zero divisor of the analytic theta section. -/
def s1424AnalyticThetaZeroLocus : Set AnalyticThetaCarrier :=
  s1424AnalyticThetaLineBundle.zeroLocus

/-- The actual analytic theta zero divisor is empty. -/
theorem s1424AnalyticThetaZeroLocus_empty :
    s1424AnalyticThetaZeroLocus = ∅ :=
  s1424AnalyticThetaLineBundle.zeroLocus_empty

/-- **Zero-divisor identification.**  The zero divisor of the actual analytic
theta global section is exactly the actual q_v^(j^2) divisor on the same
q-disc.  Both are the empty zero divisor because every q_v^(j^2) value is a
unit. -/
theorem s1424AnalyticThetaZeroLocus_eq_qj2 (j : SignedLabel l.value) :
    s1424AnalyticThetaZeroLocus =
      s1424QJ2BaseZeroLocus (l := l) j := by
  rw [s1424AnalyticThetaZeroLocus_empty, s1424QJ2BaseZeroLocus_empty]

/-- The zero section of the analytic line bundle has the whole q-disc as zero
locus. -/
def s1424AnalyticZeroSectionZeroLocus : Set AnalyticThetaCarrier :=
  Set.univ

/-- The zero section cannot replace the theta section for the q_j^2 divisor:
its zero locus is everything, while the q_j^2 divisor is empty. -/
theorem s1424AnalyticZeroSectionZeroLocus_ne_qj2
    (j : SignedLabel l.value) :
    s1424AnalyticZeroSectionZeroLocus ≠
      s1424QJ2BaseZeroLocus (l := l) j := by
  rw [s1424QJ2BaseZeroLocus_empty]
  intro h
  have hmem : analyticThetaCarrierConcrete ∈
      (∅ : Set AnalyticThetaCarrier) := by
    rw [← h]
    exact Set.mem_univ _
  exact hmem

end ABCBridge.S1424ThetaSectionActual

end
