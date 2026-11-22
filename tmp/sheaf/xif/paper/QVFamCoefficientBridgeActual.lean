import tmp.sheaf.xif.paper.QVPilotLatticeCoefficientPositiveActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange

/-!
# qVFamily lattice coefficient / local magnitude bridge

The coefficient `qVFamilyLatticeCoefficient` includes the local residue degree;
the actual local magnitude of qVFamily is `order * log(residueNormBase F-place)`.
By `log_residueNormBase_eq_residueDegree_mul` these are the same number:

  c_b * log p_b = localLogMagnitude(qVFamily T b).

This is the missing coefficient bridge for the paper target.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.QVFamCoefficientBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.NativeQVPilotNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.QVPilotLatticeCoefficientPositiveActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.ArithmeticQPilotLogVolume

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The actual coefficient identity: c_b * log p_b is the qVFamily local
log-magnitude. -/
theorem qVFamilyLatticeCoefficient_mul_logp_eq_localMagnitude
    (b : Bad (nativePlaceSelection T)) :
    qVFamilyLatticeCoefficient T b *
        Real.log (qVFamilyResiduePrime T b : Real) =
      localLogMagnitude (qVFamily T b) := by
  unfold qVFamilyLatticeCoefficient qVFamilyBasePLogCoefficient
    qVFamilyResiduePrime
  have hlogp : Real.log
      (NumberFieldFinitePlace.residueCharacteristic b.1 : Real) ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one
    · exact_mod_cast (NumberFieldFinitePlace.residueCharacteristic_pos b.1)
    · exact_mod_cast (NumberFieldFinitePlace.residueCharacteristic_prime b.1).ne_one
  field_simp [hlogp]
  rw [localLogMagnitude_eq_order_mul_log (parameter := qVFamily T b)]
  rw [log_residueNormBase_eq_residueDegree_mul
    (k := T.arithmetic.Fmod) ((nativeBadLift T).lift b)]
  rw [(nativeBadLift T).lift_comap b]
  ring

/-- The local q-pilot log is the negative local magnitude. -/
theorem localQPilotLog_eq_neg_localMagnitude
    (b : Bad (nativePlaceSelection T)) :
    localQPilotLog T b = -localLogMagnitude (qVFamily T b) := by
  unfold localQPilotLog
  rw [show -qVFamilyLatticeCoefficient T b *
        Real.log (qVFamilyResiduePrime T b : Real) =
      -(qVFamilyLatticeCoefficient T b *
        Real.log (qVFamilyResiduePrime T b : Real)) by ring]
  rw [qVFamilyLatticeCoefficient_mul_logp_eq_localMagnitude]

end LeanFormal.IUT.XiFPaper.QVFamCoefficientBridgeActual

end
