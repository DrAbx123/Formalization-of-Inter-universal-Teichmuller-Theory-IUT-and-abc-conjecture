import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Audit: the normalized qVFamily coefficient versus the qVFamily order

QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient is

  c_norm = -logb_p ||qVFamNormalizedGenerator||,

where the norm is the one on CommonPrimeCompletion (= NormalizedCompletion =
the spectral norm, Mathlib spectralNorm over PadicScalarField), *not* the
canonical valuation norm of NumberFieldFinitePlace.Completion.

This file records the exact condition under which c_norm equals the discrete
order order(qVFamily):

* qVFamNormalizedCoefficient_eq_neg_of_norm: if the normalized norm of the
  generator is p ^ x, then c_norm = -x (pure Real.logb_rpow algebra);
* qVFamNormalizedCoefficient_eq_order_iff_norm: consequently
  c_norm = order iff ||g|| = p ^ (-(order));
* qVFamNormalizedCoefficient_eq_order_div_of_norm: if
  ||g|| = p ^ (-(order / e)), then c_norm = order / e.  (The normalized
  norm/valuation formula predicts exactly this with e the ramification index of
  the place over its rational prime, so the expected value of c_norm is
  order / e, not order.)

For contrast, the *canonical* completion norm satisfies the unconditionally
proved formula ||q|| = residueNormBase ^ (-exponent) (Mathlib
NumberField.FinitePlace.norm_def; tree
ArithmeticQPilotBaseChange.qNorm_eq_residueNormBase_zpow), and
localLogMagnitude = order * log (residueNormBase)
(ArithmeticQPilotBaseChange.localLogMagnitude_eq_order_mul_log).  Hence the
canonical coefficient is order * log_p (residueNormBase) = order * f, not
order.  The order itself is recovered only after dividing by
log (residueNormBase) (ArithmeticQPilotBaseChange.orderNormalizedMagnitude_eq_order).

No norm identity is asserted here.  The missing analytic input is exactly the
normalized norm/valuation formula NormValuationCompatible (frozen card
normalizedCompletionNormValuationFormulaCard in
LeanFormal.IUT.IUTII.Frobenioid.Example36CompletionNormFormula), which says
||x|| = p ^ (-(nu(x)/e)) for the normalized norm.

No sorry/axiom/inequality. -/

noncomputable section

open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientOrderAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.ArithmeticQPilotBaseChange

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

theorem qVFamTensorP_pos : (0 : Real) < (qVFamTensorP T b : Real) := by
  have hprime : Nat.Prime (qVFamTensorP T b) :=
    Fact.out (p := Nat.Prime (qVFamTensorP T b))
  exact_mod_cast hprime.pos

theorem qVFamTensorP_one_lt : (1 : Real) < (qVFamTensorP T b : Real) := by
  have hprime : Nat.Prime (qVFamTensorP T b) :=
    Fact.out (p := Nat.Prime (qVFamTensorP T b))
  exact_mod_cast hprime.one_lt

theorem qVFamTensorP_ne_one : (qVFamTensorP T b : Real) ≠ 1 :=
  ne_of_gt (qVFamTensorP_one_lt T b)

/-- The definitional reading: the normalized coefficient is minus the p-logb of
the normalized (spectral) norm of the actual generator. -/
theorem qVFamNormalizedCoefficient_eq :
    qVFamNormalizedCoefficient T b =
      -Real.logb (qVFamTensorP T b : Real) ‖qVFamNormalizedGenerator T b‖ := rfl

/-- Pure logb algebra: if the normalized norm of the generator is p ^ x, then
the normalized coefficient is -x. -/
theorem qVFamNormalizedCoefficient_eq_neg_of_norm
    (x : Real)
    (h : ‖qVFamNormalizedGenerator T b‖ = (qVFamTensorP T b : Real) ^ x) :
    qVFamNormalizedCoefficient T b = -x := by
  unfold qVFamNormalizedCoefficient
  rw [h, Real.logb_rpow (qVFamTensorP_pos T b) (qVFamTensorP_ne_one T b)]

/-- The coefficient equals the order exactly when the normalized norm of the
generator is p ^ (-(order)). -/
theorem qVFamNormalizedCoefficient_eq_order_iff_norm :
    qVFamNormalizedCoefficient T b = ((qVFamily T b).order : Real) ↔
      ‖qVFamNormalizedGenerator T b‖ =
        (qVFamTensorP T b : Real) ^ (-(((qVFamily T b).order : Real))) := by
  constructor
  · intro h
    have hnorm := qVFamNormalizedGenerator_norm T b
    rw [h] at hnorm
    exact hnorm
  · intro h
    simpa using qVFamNormalizedCoefficient_eq_neg_of_norm T b _ h

/-- Conditional form: the order is the coefficient provided the normalized
norm is p ^ (-(order)). -/
theorem qVFamNormalizedCoefficient_eq_order_of_norm
    (h : ‖qVFamNormalizedGenerator T b‖ =
      (qVFamTensorP T b : Real) ^ (-(((qVFamily T b).order : Real)))) :
    qVFamNormalizedCoefficient T b = ((qVFamily T b).order : Real) :=
  (qVFamNormalizedCoefficient_eq_order_iff_norm T b).mpr h

/-- If the normalized norm is p ^ (-(order / e)), the normalized coefficient
is order / e.  With the value e of the normalized norm/valuation formula (the
ramification index of the place over its rational prime) this gives
c_norm = order / e, so the claimed equality c_norm = order holds only for
e = 1. -/
theorem qVFamNormalizedCoefficient_eq_order_div_of_norm
    (e : Real)
    (h : ‖qVFamNormalizedGenerator T b‖ =
      (qVFamTensorP T b : Real) ^ (-(((qVFamily T b).order : Real) / e))) :
    qVFamNormalizedCoefficient T b = ((qVFamily T b).order : Real) / e := by
  rw [qVFamNormalizedCoefficient_eq_neg_of_norm T b _ h]
  ring

/-- The canonical (default) completion coefficient of the actual qVFamily q:
minus the p-logb of the canonical valuation norm.  This is the coefficient that
QVFamPureFractionalScalingDataGapActual.qVFamPureCoefficient computes. -/
noncomputable def qVFamDefaultCoefficient : Real :=
  -Real.logb (qVFamTensorP T b : Real) ‖(qVFamily T b).q‖

/-- The canonical norm coefficient is the order times the base-p logarithm of
the residue norm, unconditionally.  With residueNormBase = p ^ f this is
order * f, not order. -/
theorem qVFamDefaultCoefficient_eq_order_mul :
    qVFamDefaultCoefficient T b =
      ((qVFamily T b).order : Real) *
        (Real.log (residueNormBase (qVFamTensorPlace T b)) /
          Real.log (qVFamTensorP T b : Real)) := by
  have hlogp : Real.log (qVFamTensorP T b : Real) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (qVFamTensorP_pos T b)
      (qVFamTensorP_ne_one T b)
  have hmagnitude :
      localLogMagnitude (qVFamily T b) =
        ((qVFamily T b).order : Real) *
          Real.log (residueNormBase (qVFamTensorPlace T b)) :=
    localLogMagnitude_eq_order_mul_log (parameter := qVFamily T b)
  have hlogq : Real.log ‖(qVFamily T b).q‖ =
      -localLogMagnitude (qVFamily T b) :=
    localSignedLog_eq_neg_magnitude (qVFamily T b)
  unfold qVFamDefaultCoefficient
  rw [Real.logb, hlogq, hmagnitude]
  field_simp

/-- The instance selected for the normalized generator is the spectral norm of
Mathlib over the p-adic scalar field, not the canonical valuation norm of the
plain completion.  This is the object-level fact behind the coefficient
definition (checked at the same reducible-definition transparency as the
definition itself). -/
theorem commonPrimeCompletion_norm_eq_spectralNorm
    {K : Type} [Field K] [NumberField K] (place : NumberField.FinitePlace K)
    (x : CommonPrimeCompletion (K := K) (p := (completionRationalPrime place).val)
      ⟨place, rfl⟩) :
    ‖x‖ = spectralNorm (PadicScalarField place) (NormalizedCompletion place) x := rfl


end LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientOrderAuditActual