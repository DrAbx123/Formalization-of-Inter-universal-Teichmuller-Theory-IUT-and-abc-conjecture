import tmp.sheaf.xif.paper.NativeQVPilotNormalizedLogVolumeActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange

/-! # Positivity of the actual qVFamily lattice coefficient and local log

For each native bad place b:

  qVFamilyResiduePrime b = residueCharacteristic b.1,
  qVFamilyBasePLogCoefficient b =
    log(residueNormBase b.1) / log(qVFamilyResiduePrime b),
  qVFamilyLatticeCoefficient b =
    order(qVFamily T b) * localResidueDegree(lift b) * basePLogCoefficient b.

The order, local residue degree, base residue log and residue-prime log are all
positive, so c_b > 0.  The local q-pilot log is

  localQPilotLog b = -(c_b * log p_b),

which equals localSignedLog(qVFamily T b), is negative and nonzero.  This gives
the actual PerB scalar connection.

No fake inequality or axiom/sorry. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.QVPilotLatticeCoefficientPositiveActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.NativeQVPilotNormalizedLogVolumeActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.ArithmeticQPilotLogVolume

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The actual residue characteristic p_b of b.1. -/
noncomputable def qVFamilyResiduePrime (b : Bad (nativePlaceSelection T)) : Nat :=
  NumberFieldFinitePlace.residueCharacteristic b.1

/-- The actual base residue degree in p_b-log units. -/
noncomputable def qVFamilyBasePLogCoefficient (b : Bad (nativePlaceSelection T)) : Real :=
  Real.log (residueNormBase b.1) /
    Real.log (qVFamilyResiduePrime T b : Real)

/-- The actual qVFamily lattice coefficient c_b. -/
noncomputable def qVFamilyLatticeCoefficient (b : Bad (nativePlaceSelection T)) : Real :=
  ((qVFamily T b).order : Real) *
    (localResidueDegree (k := T.arithmetic.Fmod)
      ((nativeBadLift T).lift b) : Real) *
    qVFamilyBasePLogCoefficient T b

/-- The actual local q-pilot log: -(c_b log p_b). -/
noncomputable def localQPilotLog (b : Bad (nativePlaceSelection T)) : Real :=
  -qVFamilyLatticeCoefficient T b *
    Real.log (qVFamilyResiduePrime T b : Real)

/-- qVFamily order is positive. -/
theorem qVFamilyOrder_pos (b : Bad (nativePlaceSelection T)) :
    0 < (qVFamily T b).order :=
  (qVFamily T b).order_pos

/-- Local residue degree is positive. -/
theorem qVFamilyLocalResidueDegree_pos (b : Bad (nativePlaceSelection T)) :
    0 < localResidueDegree (k := T.arithmetic.Fmod)
      ((nativeBadLift T).lift b) :=
  localResidueDegree_pos (k := T.arithmetic.Fmod) ((nativeBadLift T).lift b)

/-- The residue prime is positive. -/
theorem qVFamilyResiduePrime_pos (b : Bad (nativePlaceSelection T)) :
    0 < qVFamilyResiduePrime T b :=
  NumberFieldFinitePlace.residueCharacteristic_pos b.1

/-- The residue-prime logarithm is positive. -/
theorem qVFamilyResiduePrime_log_pos (b : Bad (nativePlaceSelection T)) :
    0 < Real.log (qVFamilyResiduePrime T b : Real) := by
  apply Real.log_pos
  have hprime : Nat.Prime (qVFamilyResiduePrime T b) :=
    NumberFieldFinitePlace.residueCharacteristic_prime b.1
  exact_mod_cast hprime.one_lt

/-- The base p-log coefficient is positive. -/
theorem qVFamilyBasePLogCoefficient_pos (b : Bad (nativePlaceSelection T)) :
    0 < qVFamilyBasePLogCoefficient T b := by
  unfold qVFamilyBasePLogCoefficient
  exact div_pos (Real.log_pos (residueNormBase_gt_one b.1))
    (qVFamilyResiduePrime_log_pos T b)

/-- The actual qVFamily lattice coefficient is positive. -/
theorem qVFamilyLatticeCoefficient_pos (b : Bad (nativePlaceSelection T)) :
    0 < qVFamilyLatticeCoefficient T b := by
  unfold qVFamilyLatticeCoefficient
  have horder : (0 : Real) < ((qVFamily T b).order : Real) := by
    exact_mod_cast qVFamilyOrder_pos T b
  have hdegree : (0 : Real) <
      (localResidueDegree (k := T.arithmetic.Fmod)
        ((nativeBadLift T).lift b) : Real) := by
    exact_mod_cast qVFamilyLocalResidueDegree_pos T b
  exact mul_pos (mul_pos horder hdegree)
    (qVFamilyBasePLogCoefficient_pos T b)

/-- The actual local q-pilot log is exactly -(c_b log p_b). -/
theorem localQPilotLog_eq_neg_coefficient_mul_log
    (b : Bad (nativePlaceSelection T)) :
    localQPilotLog T b =
      -qVFamilyLatticeCoefficient T b *
        Real.log (qVFamilyResiduePrime T b : Real) := rfl

/-- The local q-pilot log is negative. -/
theorem localQPilotLog_neg (b : Bad (nativePlaceSelection T)) :
    localQPilotLog T b < 0 := by
  rw [localQPilotLog_eq_neg_coefficient_mul_log]
  have hc := qVFamilyLatticeCoefficient_pos T b
  have hp := qVFamilyResiduePrime_log_pos T b
  have hprod : 0 < qVFamilyLatticeCoefficient T b *
      Real.log (qVFamilyResiduePrime T b : Real) := mul_pos hc hp
  linarith

/-- The local q-pilot log is nonzero. -/
theorem localQPilotLog_ne_zero (b : Bad (nativePlaceSelection T)) :
    localQPilotLog T b ≠ 0 :=
  ne_of_lt (localQPilotLog_neg T b)

/-- Actual PerB scalar data from the positive qVFamily coefficient. -/
structure QVPilotPerBScalarData
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T))
    [Fintype (Bad (nativePlaceSelection T))] where
  coefficient : Real
  coefficient_eq : coefficient = qVFamilyLatticeCoefficient T b
  coefficient_pos : 0 < coefficient
  residuePrime : Nat
  residuePrime_eq : residuePrime = qVFamilyResiduePrime T b
  localLog : Real
  localLog_eq : localLog = localQPilotLog T b
  localLog_eq_neg_coefficient_log :
    localLog = -coefficient * Real.log (residuePrime : Real)
  localLog_ne_zero : localLog ≠ 0

/-- The actual PerB scalar data constructor. -/
noncomputable def qvPilotPerBScalarData :
    QVPilotPerBScalarData T b where
  coefficient := qVFamilyLatticeCoefficient T b
  coefficient_eq := rfl
  coefficient_pos := qVFamilyLatticeCoefficient_pos T b
  residuePrime := qVFamilyResiduePrime T b
  residuePrime_eq := rfl
  localLog := localQPilotLog T b
  localLog_eq := rfl
  localLog_eq_neg_coefficient_log := rfl
  localLog_ne_zero := localQPilotLog_ne_zero T b

end LeanFormal.IUT.XiFPaper.QVPilotLatticeCoefficientPositiveActual

end
