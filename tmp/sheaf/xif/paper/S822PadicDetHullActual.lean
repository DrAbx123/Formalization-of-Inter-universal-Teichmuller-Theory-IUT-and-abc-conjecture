import tmp.sheaf.xif.paper.S793PaperLeastLambdaOHullActual
import tmp.sheaf.xif.paper.S799LeastLambdaOPaperTargetActual
import tmp.sheaf.xif.paper.S782FiniteRootStackExtensionActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceStepVAssembly
import Mathlib.NumberTheory.Padics.PadicNumbers

/-! # S822: p-adic determinant / Monge-Ampere analogue for the least lambda*O hull

Task W5.  The archimedean (quaternionic) Monge-Ampere route of Task P was
rejected in S743 as archimedean.  This file constructs the *p-adic* determinant
analogue that actually exists and records exactly what it proves and what it
cannot prove for the paper-faithful least lambda*O hull log.

The p-adic determinant is the Haar scaling character
(MeasureTheory.distribHaarChar), the modulus of the multiplication operator.
Its logarithm is additive in the multiplicative exponent, so the p-adic
Monge-Ampere operator (the second difference of the log-volume in the
coefficient) vanishes identically.  In particular the p-adic log-volume is
affine, not strictly concave: concavity statements degenerate to equalities.

New content, all actual:
* normalizedLogVolume_smul_canonicalUnitReference:
  log-volume of a scaled canonical lattice = log of the p-adic determinant.
* normalizedLogVolume_smul_pow / ..._eq_of_pow_eq: the p-adic determinant
  is Z-linear in the exponent (the 2l-th root of the determinant).
* arithmeticTuplePureFractionalScalingData_add / ..._zero: scaling data is
  closed under addition and contains zero (actual generators, no fake data).
* normalizedLogVolume_lambdaOSet_add / ..._zero /
  normalizedLogVolume_secondDifference_zero: the p-adic MA operator is zero.
* paperRootCoefficient_twoL_mul: the paper coefficient is order/(2l), so the
  paper hull log is the normalized log of the 2l-th root of the determinant.
* padic_no_sqrt_prime: no square root of p in Q_p (the value-group
  obstruction to interpolating coefficients / to a midpoint concavity).
* no_mu2l_sqrt_neg_one: for l odd there is no zeta in mu_{2l} with
  zeta^2 = -1 in a char-zero field.  This is the concrete obstruction to a
  quaternionic structure coming from the finite root stack.

No target change, no surrogate, no axiom, no sorry.  The file does not assert
the remaining paper gaps (completion root at order/(2l), c_norm = order,
hull equality); those remain exact and are only located here.
-/

noncomputable section
open scoped BigOperators Pointwise NNReal ENNReal
set_option linter.overlappingInstances false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S822PadicDetHullActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.S799LeastLambdaOPaperTargetActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- The paper least lambda*O region at coefficient c. -/
noncomputable abbrev lambdaOSet (c : qVFamTensorV → ℝ) : Set (qVFamTensorBlock T b) :=
  paperLambdaORegion (l := l) T b c

/-- Units of the tensor block act continuously by multiplication. -/
local instance lambdaOUnitsContinuousConstSMul :
    ContinuousConstSMul (qVFamTensorBlock T b)ˣ (qVFamTensorBlock T b) := by
  refine ⟨fun u => ?_⟩
  change Continuous (fun x : qVFamTensorBlock T b =>
    (u : qVFamTensorBlock T b) * x)
  exact (LinearMap.mulLeft ℚ_[qVFamTensorP T b]
    (u : qVFamTensorBlock T b)).continuous_of_finiteDimensional

/-- **The p-adic determinant.**  The Haar scaling character of the unit group:
for a unit u and additive Haar mu, mu (u • s) = padicDet mu u * mu s.
This is the p-adic analogue of |det|: for a scalar unit it is its norm to
the power of the degree, and it is a monoid homomorphism. -/
noncomputable def padicDet (μ : Measure (qVFamTensorBlock T b))
    [Measure.IsAddHaarMeasure μ] : (qVFamTensorBlock T b)ˣ →* ℝ≥0 :=
  MeasureTheory.distribHaarChar (qVFamTensorBlock T b)

theorem padicDet_pos (μ : Measure (qVFamTensorBlock T b))
    [Measure.IsAddHaarMeasure μ] (u : (qVFamTensorBlock T b)ˣ) :
    0 < padicDet (l := l) T b μ u :=
  MeasureTheory.distribHaarChar_pos

theorem padicDet_mul (μ : Measure (qVFamTensorBlock T b))
    [Measure.IsAddHaarMeasure μ] (u v : (qVFamTensorBlock T b)ˣ) :
    padicDet (l := l) T b μ (u * v) =
      padicDet (l := l) T b μ u * padicDet (l := l) T b μ v :=
  map_mul (padicDet (l := l) T b μ) u v

theorem padicDet_pow (μ : Measure (qVFamTensorBlock T b))
    [Measure.IsAddHaarMeasure μ] (u : (qVFamTensorBlock T b)ˣ) (n : ℕ) :
    padicDet (l := l) T b μ (u ^ n) = padicDet (l := l) T b μ u ^ n :=
  map_pow (padicDet (l := l) T b μ) u n

/-- **Log-volume = log of the p-adic determinant.**  For any unit u of the
tensor block, the degree-normalized log-volume of the scaled canonical lattice
u • O is the logarithm of the p-adic determinant of u (divided by the degree,
which is the IUT IV Proposition 1.4(i) normalization). -/
theorem normalizedLogVolume_smul_canonicalUnitReference
    (μ : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure μ]
    [Measure.Regular μ] (u : (qVFamTensorBlock T b)ˣ) :
    arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple μ
        (u • arithmeticTupleCanonicalUnitReference
          (qVFamTensorPlaces T b) qVFamTensorTuple) =
      (1 / (Module.finrank ℚ_[qVFamTensorP T b]
        (qVFamTensorBlock T b) : ℝ)) *
        Real.log (padicDet (l := l) T b μ u : ℝ) := by
  set O := arithmeticTupleCanonicalUnitReference
    (qVFamTensorPlaces T b) qVFamTensorTuple with hO
  have hμO := measure_arithmeticTupleCanonicalRegions_pos_lt_top
    (places := qVFamTensorPlaces T b) (tuple := qVFamTensorTuple) μ
  have hOpos : 0 < μ O := hμO.2.1
  have hOfin : μ O < ⊤ := hμO.2.2
  have hdetpos : 0 < padicDet (l := l) T b μ u := padicDet_pos (l := l) T b μ u
  have hmul : (μ (u • O)) =
      (padicDet (l := l) T b μ u : ℝ≥0∞) * μ O :=
    (MeasureTheory.distribHaarChar_mul (A := qVFamTensorBlock T b)
      (G := (qVFamTensorBlock T b)ˣ) (μ := μ) (g := u) (s := O)).symm
  have hcast : (μ (u • O)).toReal =
      (padicDet (l := l) T b μ u : ℝ) * (μ O).toReal := by
    rw [hmul, ENNReal.toReal_mul, ENNReal.coe_toReal]
  have hdetne : (padicDet (l := l) T b μ u : ℝ) ≠ 0 := by
    exact_mod_cast hdetpos.ne'
  have hOne : (μ O).toReal ≠ 0 :=
    (ENNReal.toReal_pos hOpos.ne' hOfin.ne).ne'
  unfold arithmeticTupleNormalizedLogVolume
  rw [hcast, Real.log_mul hdetne hOne]
  ring

/-- **The p-adic determinant is Z-linear in the exponent.**  Taking powers
multiplies the log-volume by the exponent: log det (u^n) = n log det u. -/
theorem normalizedLogVolume_smul_pow
    (μ : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure μ]
    [Measure.Regular μ] (u : (qVFamTensorBlock T b)ˣ) (n : ℕ) :
    arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple μ
        ((u ^ n) • arithmeticTupleCanonicalUnitReference
          (qVFamTensorPlaces T b) qVFamTensorTuple) =
      (n : ℝ) * arithmeticTupleNormalizedLogVolume
        (qVFamTensorPlaces T b) qVFamTensorTuple μ
        (u • arithmeticTupleCanonicalUnitReference
          (qVFamTensorPlaces T b) qVFamTensorTuple) := by
  rw [normalizedLogVolume_smul_canonicalUnitReference,
    normalizedLogVolume_smul_canonicalUnitReference]
  have hdet : (padicDet (l := l) T b μ (u ^ n) : ℝ) =
      (padicDet (l := l) T b μ u : ℝ) ^ n := by
    rw [padicDet_pow, NNReal.coe_pow]
  rw [hdet, Real.log_pow]
  ring

/-- **Root of the p-adic determinant.**  If v is an n-th root of u, then
the log-volume of u • O is n times the log-volume of v • O.  This is the
p-adic analogue of the paper q^(1/2l) root and is the only sense in which a
2l-th root of the determinant exists. -/
theorem normalizedLogVolume_smul_eq_of_pow_eq
    (μ : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure μ]
    [Measure.Regular μ] (u v : (qVFamTensorBlock T b)ˣ) (n : ℕ) (h : v ^ n = u) :
    arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple μ
        (u • arithmeticTupleCanonicalUnitReference
          (qVFamTensorPlaces T b) qVFamTensorTuple) =
      (n : ℝ) * arithmeticTupleNormalizedLogVolume
        (qVFamTensorPlaces T b) qVFamTensorTuple μ
        (v • arithmeticTupleCanonicalUnitReference
          (qVFamTensorPlaces T b) qVFamTensorTuple) := by
  rw [← h, normalizedLogVolume_smul_pow]

/-! ## p-adic Monge-Ampere: the second difference vanishes -/

/-- The log-volume functional of the exact hull formula, as a function of the
coefficient: - (sum c) log p. -/
noncomputable def hullLogFunctional (c : qVFamTensorV → ℝ) : ℝ :=
  -((∑ i, c i) * Real.log (qVFamTensorP T b : ℝ))

theorem hullLogFunctional_add (c c' : qVFamTensorV → ℝ) :
    hullLogFunctional (l := l) T b (c + c') =
      hullLogFunctional (l := l) T b c + hullLogFunctional (l := l) T b c' := by
  unfold hullLogFunctional
  simp only [Pi.add_apply, Finset.sum_add_distrib]
  ring

theorem hullLogFunctional_zero :
    hullLogFunctional (l := l) T b (0 : qVFamTensorV → ℝ) = 0 := by
  unfold hullLogFunctional
  simp

theorem hullLogFunctional_smul (k : ℝ) (c : qVFamTensorV → ℝ) :
    hullLogFunctional (l := l) T b (fun i => k * c i) =
      k * hullLogFunctional (l := l) T b c := by
  unfold hullLogFunctional
  rw [← Finset.mul_sum]
  ring

/-- Explicit scaling data at the sum of two coefficients, built from actual
generators: the pure tensor of the product generators has norm p^(-(c+c')).
No field is invented. -/
noncomputable def arithmeticTuplePureFractionalScalingData_add
    {c c' : qVFamTensorV → ℝ}
    (d : ArithmeticTuplePureFractionalScalingData
      (qVFamTensorPlaces T b) qVFamTensorTuple c)
    (d' : ArithmeticTuplePureFractionalScalingData
      (qVFamTensorPlaces T b) qVFamTensorTuple c') :
    ArithmeticTuplePureFractionalScalingData
      (qVFamTensorPlaces T b) qVFamTensorTuple (c + c') :=
  arithmeticTuplePureFractionalScalingData_ofGenerator
    (qVFamTensorPlaces T b) qVFamTensorTuple (c + c')
    (fun i => d.localGenerator i * d'.localGenerator i)
    (fun i => by
      rw [norm_mul, d.localGenerator_norm i, d'.localGenerator_norm i,
        ← Real.rpow_add (show (0 : ℝ) < (qVFamTensorP T b : ℝ) from
          by exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).pos)]
      congr 1
      simp only [Pi.add_apply]
      ring)

/-- Explicit scaling data at coefficient zero: the unit generator. -/
noncomputable def arithmeticTuplePureFractionalScalingData_zero :
    ArithmeticTuplePureFractionalScalingData
      (qVFamTensorPlaces T b) qVFamTensorTuple (0 : qVFamTensorV → ℝ) :=
  arithmeticTuplePureFractionalScalingData_ofGenerator
    (qVFamTensorPlaces T b) qVFamTensorTuple 0 (fun _ => 1)
    (fun i => by
      simp)

/-- Exact hull-formula log-volume on the least lambda*O region. -/
theorem normalizedLogVolume_lambdaOSet
    (μ : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure μ]
    {c : qVFamTensorV → ℝ}
    (d : ArithmeticTuplePureFractionalScalingData
      (qVFamTensorPlaces T b) qVFamTensorTuple c) :
    arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple μ
        (lambdaOSet (l := l) T b c) =
      hullLogFunctional (l := l) T b c :=
  arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic
    (qVFamTensorPlaces T b) qVFamTensorTuple μ d

/-- **Additivity of the p-adic log-volume on the coefficient lattice.**  Only
data at c and at c' is needed; data at c+c' is constructed. -/
theorem normalizedLogVolume_lambdaOSet_add
    (μ : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure μ]
    {c c' : qVFamTensorV → ℝ}
    (d : ArithmeticTuplePureFractionalScalingData
      (qVFamTensorPlaces T b) qVFamTensorTuple c)
    (d' : ArithmeticTuplePureFractionalScalingData
      (qVFamTensorPlaces T b) qVFamTensorTuple c') :
    arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple μ
        (lambdaOSet (l := l) T b (c + c')) =
      arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple μ
        (lambdaOSet (l := l) T b c) +
      arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple μ
        (lambdaOSet (l := l) T b c') := by
  rw [normalizedLogVolume_lambdaOSet (l := l) T b μ
        (arithmeticTuplePureFractionalScalingData_add (l := l) T b d d'),
      normalizedLogVolume_lambdaOSet (l := l) T b μ d,
      normalizedLogVolume_lambdaOSet (l := l) T b μ d']
  exact hullLogFunctional_add (l := l) T b c c'

/-- The log-volume at coefficient zero vanishes. -/
theorem normalizedLogVolume_lambdaOSet_zero
    (μ : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure μ] :
    arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple μ
        (lambdaOSet (l := l) T b (0 : qVFamTensorV → ℝ)) = 0 := by
  rw [normalizedLogVolume_lambdaOSet (l := l) T b μ
        (arithmeticTuplePureFractionalScalingData_zero (l := l) T b)]
  exact hullLogFunctional_zero (l := l) T b

/-- **The p-adic Monge-Ampere operator vanishes.**  The second difference of
the normalized log-volume along the coefficient lattice is identically zero:
the p-adic determinant is affine, there is no curvature and no strict
concavity. -/
theorem normalizedLogVolume_secondDifference_zero
    (μ : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure μ]
    {c c' : qVFamTensorV → ℝ}
    (d : ArithmeticTuplePureFractionalScalingData
      (qVFamTensorPlaces T b) qVFamTensorTuple c)
    (d' : ArithmeticTuplePureFractionalScalingData
      (qVFamTensorPlaces T b) qVFamTensorTuple c') :
    arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple μ
        (lambdaOSet (l := l) T b (c + c')) -
      arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple μ
        (lambdaOSet (l := l) T b c) -
      arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple μ
        (lambdaOSet (l := l) T b c') +
      arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple μ
        (lambdaOSet (l := l) T b (0 : qVFamTensorV → ℝ)) = 0 := by
  rw [normalizedLogVolume_lambdaOSet_add (l := l) T b μ d d',
    normalizedLogVolume_lambdaOSet_zero (l := l) T b μ]
  ring

/-! ## Paper coefficient: the 2l-th root of the p-adic determinant -/

/-- The paper coefficient order/(2l) is exactly the 2l-th root of the
classical q-parameter coefficient. -/
theorem paperRootCoefficient_twoL_mul :
    (2 * (l.value : ℝ)) * paperRootCoefficientFamily (l := l) T b () =
      ((qVFamily T b).order : ℝ) := by
  unfold paperRootCoefficientFamily qVFamPaperRootCoefficient
  have hl : (l.value : ℝ) ≠ 0 := by exact_mod_cast l.prime.ne_zero
  have hl2 : (2 * (l.value : ℝ)) ≠ 0 := by positivity
  field_simp

/-- In log form: the classical coefficient log is 2l times the paper root
coefficient log. -/
theorem hullLogFunctional_twoL_mul :
    (2 * (l.value : ℝ)) * hullLogFunctional (l := l) T b
        (paperRootCoefficientFamily (l := l) T b) =
      -(((qVFamily T b).order : ℝ) *
        Real.log (qVFamTensorP T b : ℝ)) := by
  unfold hullLogFunctional paperRootCoefficientFamily qVFamPaperRootCoefficient
  have hsum : (∑ _ : qVFamTensorV,
      ((qVFamily T b).order : ℝ) / (2 * (l.value : ℝ))) =
      ((qVFamily T b).order : ℝ) / (2 * (l.value : ℝ)) := by
    simp
  rw [hsum]
  have hl : (l.value : ℝ) ≠ 0 := by exact_mod_cast l.prime.ne_zero
  have hl2 : (2 * (l.value : ℝ)) ≠ 0 := by positivity
  field_simp

/-! ## Quaternionic no-go: no order-4 root of unity in mu_{2l} -/

/-- **No quaternionic unit i from the root stack.**  For l odd (all primes
>= 5) there is no element of order 4 in mu_{2l}: an element satisfying the
quaternionic relation zeta^2 = -1 cannot satisfy zeta^(2l) = 1 in a
characteristic-zero field.  Hence the finite root stack of S782 carries no
quaternionic structure coming from roots of unity. -/
theorem no_mu2l_sqrt_neg_one {F : Type*} [Field F] [CharZero F] {ζ : F}
    (hζ : ζ ^ (2 * l.value) = 1) : ζ ^ 2 ≠ -1 := by
  intro h2
  have hpow : ζ ^ (2 * l.value) = (ζ ^ 2) ^ l.value := by
    rw [← pow_mul]
  rw [hpow, h2, (l.odd).neg_one_pow] at hζ
  have htwo : (2 : F) = 0 := by
    have h : (1 : F) + 1 = 0 := eq_neg_iff_add_eq_zero.mp hζ.symm
    rwa [one_add_one_eq_two] at h
  exact (Nat.cast_ne_zero.mpr (by norm_num : (2 : ℕ) ≠ 0)) htwo

/-- The same no-go on the actual finite root-stack extension L(mu_{2l}). -/
theorem rootStack_no_mu2l_sqrt_neg_one
    {ζ : rootStackExtension T b} (hζ : ζ ^ (2 * l.value) = 1) :
    ζ ^ 2 ≠ -1 :=
  no_mu2l_sqrt_neg_one (l := l) (F := rootStackExtension T b) hζ

/-- **Value-group obstruction to midpoint concavity.**  The p-adic determinant
has no square root of p in Q_p: the valuation is 1, which is odd, so no
generator of norm p^(-1/2) exists in the completion.  Thus interpolating a
coefficient to its midpoint (the concavity/Jensen step) requires a genuine
extension/root stack, not just a determinant identity. -/
theorem padic_no_sqrt_prime (p : ℕ) [Fact p.Prime] :
    ¬ ∃ x : ℚ_[p], x ^ 2 = (p : ℚ_[p]) := by
  rintro ⟨x, hx⟩
  have hp0 : (p : ℚ_[p]) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hx
    exact hp0 hx.symm
  have hnorm := congrArg (fun y : ℚ_[p] => ‖y‖) hx
  rw [norm_pow, Padic.norm_p, Padic.norm_eq_zpow_neg_valuation hx0] at hnorm
  have hp_pos : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast (Fact.out : p.Prime).pos
  have hp_one : (p : ℝ) ≠ 1 := by
    have : (1 : ℝ) < (p : ℝ) := by
      exact_mod_cast (Fact.out : p.Prime).one_lt
    linarith
  have hnorm' : (p : ℝ) ^ ((-(x.valuation)) * (2 : ℤ)) =
      (p : ℝ) ^ (-1 : ℤ) := by
    have hstep : (p : ℝ) ^ ((-(x.valuation)) * (2 : ℤ)) =
        ((p : ℝ) ^ (-(x.valuation))) ^ (2 : ℕ) := by
      rw [← zpow_natCast, ← zpow_mul]
      norm_num
    rw [hstep, hnorm, zpow_neg_one]
  have hz := (zpow_right_inj₀ hp_pos hp_one).mp hnorm'
  omega

end LeanFormal.IUT.XiFPaper.S822PadicDetHullActual

end

#print axioms LeanFormal.IUT.XiFPaper.S822PadicDetHullActual.normalizedLogVolume_smul_canonicalUnitReference
#print axioms LeanFormal.IUT.XiFPaper.S822PadicDetHullActual.normalizedLogVolume_smul_pow
#print axioms LeanFormal.IUT.XiFPaper.S822PadicDetHullActual.normalizedLogVolume_secondDifference_zero
#print axioms LeanFormal.IUT.XiFPaper.S822PadicDetHullActual.no_mu2l_sqrt_neg_one
#print axioms LeanFormal.IUT.XiFPaper.S822PadicDetHullActual.padic_no_sqrt_prime
