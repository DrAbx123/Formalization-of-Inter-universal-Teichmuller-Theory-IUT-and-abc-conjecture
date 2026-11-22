import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientActual
import tmp.sheaf.xif.paper.QVFamRootFactorCorrectionActual
import tmp.sheaf.xif.paper.QVFamThetaImageActual

/-! # Normalized qVFamily coefficient and the 2l-root relation

The normalized coefficient is

  qVFamNormalizedCoefficient b = order(qVFamily T b).

The root coefficient is

  qVFamPaperRootCoefficient b = order(qVFamily T b) / (2l).

This file proves the actual relation

  qVFamPaperRootCoefficient b = qVFamNormalizedCoefficient b / (2l),

and the inverse relation 2l * root = normalized.  Both the q-pilot theta
packet and the root theta data use the normalized completion norm of
qVFamily (qVFamilyQNorm / qVFamilyThetaPacket); the old full order/default-norm
coefficient is not mixed into these definitions.

No fake inequality/axiom/sorry. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.QVFamNormalizedRootRelationActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.QVFamThetaImageActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The root coefficient defined from the normalized coefficient by division
by 2l. -/
noncomputable def qVFamRootFromNormalized : Real :=
  qVFamNormalizedCoefficient T b / (2 * l.value : Real)

/-- Actual relation: the paper root coefficient is normalized/(2l). -/
theorem qVFamPaperRootCoefficient_eq_normalized_div :
    qVFamPaperRootCoefficient T b =
      qVFamRootFromNormalized T b := by
  unfold qVFamPaperRootCoefficient qVFamRootFromNormalized
    qVFamNormalizedCoefficient qVFamTensorCoefficient
  ring_nf

/-- Equivalent direct relation: paper root coefficient = order/(2l). -/
theorem qVFamPaperRootCoefficient_eq_order_div :
    qVFamPaperRootCoefficient T b =
      ((qVFamily T b).order : Real) / (2 * l.value : Real) := rfl

/-- Inverse relation: 2l times the root coefficient is the normalized
coefficient. -/
theorem qVFamRootFromNormalized_mul_denominator :
    qVFamRootFromNormalized T b * (2 * l.value : Real) =
      qVFamNormalizedCoefficient T b := by
  unfold qVFamRootFromNormalized qVFamNormalizedCoefficient
    qVFamTensorCoefficient
  have htwo : (2 * l.value : Real) ≠ 0 := by
    exact_mod_cast Nat.mul_ne_zero (by norm_num) l.prime.ne_zero
  have hl : (l.value : Real) ≠ 0 := by exact_mod_cast l.prime.ne_zero
  field_simp [htwo, hl]

/-- Actual normalized/root data, based only on the normalized coefficient. -/
structure QVFamNormalizedRootData where
  cNorm : Real
  cNorm_eq : cNorm = qVFamNormalizedCoefficient T b
  cRoot : Real
  cRoot_eq : cRoot = qVFamPaperRootCoefficient T b
  cRoot_eq_cNorm_div : cRoot = cNorm / (2 * l.value : Real)
  cNorm_eq_twoL_mul_cRoot : cNorm = (2 * l.value : Real) * cRoot
  thetaPacketQ : Real
  thetaPacketQ_eq : thetaPacketQ = qVFamilyQNorm T b

/-- The actual normalized/root data constructor. -/
noncomputable def qVFamNormalizedRootData : QVFamNormalizedRootData T b where
  cNorm := qVFamNormalizedCoefficient T b
  cNorm_eq := rfl
  cRoot := qVFamPaperRootCoefficient T b
  cRoot_eq := rfl
  cRoot_eq_cNorm_div := qVFamPaperRootCoefficient_eq_normalized_div T b
  cNorm_eq_twoL_mul_cRoot := by
    rw [qVFamPaperRootCoefficient_eq_normalized_div]
    unfold qVFamRootFromNormalized qVFamNormalizedCoefficient
      qVFamTensorCoefficient
    have htwo : (2 * l.value : Real) ≠ 0 := by
      exact_mod_cast Nat.mul_ne_zero (by norm_num) l.prime.ne_zero
    have hl : (l.value : Real) ≠ 0 := by exact_mod_cast l.prime.ne_zero
    field_simp [htwo, hl]
  thetaPacketQ := qVFamilyQNorm T b
  thetaPacketQ_eq := rfl

/-- The q-pilot theta packet uses the same normalized qVFamily norm. -/
theorem thetaPacket_q_eq_qVFamilyQNorm :
    (qVFamilyThetaPacket T b).q = qVFamilyQNorm T b := rfl

end LeanFormal.IUT.XiFPaper.QVFamNormalizedRootRelationActual

end
