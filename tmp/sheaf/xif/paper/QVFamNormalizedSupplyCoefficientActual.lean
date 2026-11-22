import tmp.sheaf.xif.paper.QVFamPureFractionalScalingDataGapActual
import tmp.sheaf.xif.paper.RootCorrectedQPilotScalarActual
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # Supply-based normalized qVFamily coefficient

Do not use the order-based QVFamNormalizedCoefficientActual definition.  The
normalized coefficient is defined from an actual normalized generator supply
(the CommonPrimeCompletion generator with the normalized spectral norm):

  c_norm = -logb_p ||g_normalized||,

so ||g_normalized|| = p^(-c_norm) by construction (Real.rpow_logb).  Both the
q-pilot and theta scalars below use this same c_norm:

  qScalar   = -c_norm * log p,
  c_root    = c_norm / (2l),
  thetaScalar = -c_root * log p = qScalar / (2l).

For c_norm >= 0, 2l >= 1, we prove c_root <= c_norm.  The supply is an explicit
input, not fabricated from the default-norm qVFamily element.

No fake inequality/axiom/sorry. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.QVFamNormalizedSupplyCoefficientActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamPureFractionalScalingDataGapActual
open LeanFormal.IUT.XiFPaper.RootCorrectedQPilotScalarActual
open LeanFormal.IUT.XiFPaper.NativeQVPilotNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable (S : NormalizedGeneratorSupply T b)

/-- Supply-based normalized coefficient c_norm = -logb_p ||g||. -/
noncomputable def qVFamSupplyNormCoefficient : Real :=
  -Real.logb (qVFamTensorP T b : Real) ‖S.generator‖

/-- The supplied normalized generator has norm p^(-c_norm). -/
theorem qVFamSupplyGenerator_norm :
    ‖S.generator‖ =
      (qVFamTensorP T b : Real) ^ (-(qVFamSupplyNormCoefficient T b S)) := by
  unfold qVFamSupplyNormCoefficient
  have hp_pos : (0 : Real) < (qVFamTensorP T b : Real) := by
    have hprime : Nat.Prime (qVFamTensorP T b) := by
      unfold qVFamTensorP
      exact (completionRationalPrime (qVFamTensorPlace T b)).property
    exact_mod_cast hprime.pos
  have hp_ne_one : (qVFamTensorP T b : Real) ≠ 1 := by
    have hprime : Nat.Prime (qVFamTensorP T b) := by
      unfold qVFamTensorP
      exact (completionRationalPrime (qVFamTensorPlace T b)).property
    exact ne_of_gt (by exact_mod_cast hprime.one_lt : (1 : Real) < (qVFamTensorP T b : Real))
  have hnorm_pos : 0 < ‖S.generator‖ := by
    rw [S.generator_norm]
    exact Real.rpow_pos_of_pos hp_pos _
  rw [neg_neg]
  exact (Real.rpow_logb hp_pos hp_ne_one hnorm_pos).symm

/-- q-pilot scalar based on the supply c_norm. -/
noncomputable def qVFamSupplyQScalar : Real :=
  -qVFamSupplyNormCoefficient T b S *
    Real.log (qVFamTensorP T b : Real)

/-- Root coefficient c_root = c_norm/(2l). -/
noncomputable def qVFamSupplyRootCoefficient : Real :=
  qVFamSupplyNormCoefficient T b S / (2 * l.value : Real)

/-- Theta root scalar based on the same supply c_norm. -/
noncomputable def qVFamSupplyThetaScalar : Real :=
  -qVFamSupplyRootCoefficient T b S *
    Real.log (qVFamTensorP T b : Real)

/-- Actual relation: c_root = c_norm/(2l). -/
theorem qVFamSupplyRootCoefficient_eq :
    qVFamSupplyRootCoefficient T b S =
      qVFamSupplyNormCoefficient T b S / (2 * l.value : Real) := rfl

/-- Actual relation: theta scalar = q scalar/(2l). -/
theorem qVFamSupplyThetaScalar_eq_div :
    qVFamSupplyThetaScalar T b S =
      qVFamSupplyQScalar T b S / (2 * l.value : Real) := by
  unfold qVFamSupplyThetaScalar qVFamSupplyQScalar qVFamSupplyRootCoefficient
  ring

/-- Nonlinear denominator is nonzero. -/
theorem qVFamSupplyDenominator_ne_zero :
    (2 * l.value : Real) ≠ 0 := by
  exact_mod_cast Nat.mul_ne_zero (by norm_num) l.prime.ne_zero

/-- The root coefficient is at most the normalized coefficient when c_norm is
nonnegative. -/
theorem qVFamSupplyRootCoefficient_le
    (hc : 0 ≤ qVFamSupplyNormCoefficient T b S) :
    qVFamSupplyRootCoefficient T b S ≤ qVFamSupplyNormCoefficient T b S := by
  unfold qVFamSupplyRootCoefficient
  have hl : (1 : Real) ≤ (2 * l.value : Real) := by
    have hpos : 0 < l.value := l.prime.pos
    exact_mod_cast (Nat.succ_le_of_lt (Nat.mul_pos (by norm_num) hpos))
  calc
    qVFamSupplyNormCoefficient T b S / (2 * l.value : Real)
        ≤ qVFamSupplyNormCoefficient T b S / 1 :=
          div_le_div_of_nonneg_left hc zero_lt_one hl
    _ = qVFamSupplyNormCoefficient T b S := div_one _

/-- Actual supply-based q/root scalar data. -/
structure QVFamSupplyScalarData where
  cNorm : Real
  cNorm_eq : cNorm = qVFamSupplyNormCoefficient T b S
  qScalar : Real
  qScalar_eq : qScalar = qVFamSupplyQScalar T b S
  cRoot : Real
  cRoot_eq : cRoot = qVFamSupplyRootCoefficient T b S
  thetaScalar : Real
  thetaScalar_eq : thetaScalar = qVFamSupplyThetaScalar T b S
  cRoot_eq_cNorm_div : cRoot = cNorm / (2 * l.value : Real)
  thetaScalar_eq_qScalar_div : thetaScalar = qScalar / (2 * l.value : Real)
  cRoot_le_cNorm : cRoot ≤ cNorm

/-- The actual supply-based data constructor, conditional on c_norm >= 0. -/
noncomputable def qVFamSupplyScalarData
    (hc : 0 ≤ qVFamSupplyNormCoefficient T b S) :
    QVFamSupplyScalarData T b S where
  cNorm := qVFamSupplyNormCoefficient T b S
  cNorm_eq := rfl
  qScalar := qVFamSupplyQScalar T b S
  qScalar_eq := rfl
  cRoot := qVFamSupplyRootCoefficient T b S
  cRoot_eq := rfl
  thetaScalar := qVFamSupplyThetaScalar T b S
  thetaScalar_eq := rfl
  cRoot_eq_cNorm_div := qVFamSupplyRootCoefficient_eq T b S
  thetaScalar_eq_qScalar_div := qVFamSupplyThetaScalar_eq_div T b S
  cRoot_le_cNorm := qVFamSupplyRootCoefficient_le T b S hc

end LeanFormal.IUT.XiFPaper.QVFamNormalizedSupplyCoefficientActual

end
