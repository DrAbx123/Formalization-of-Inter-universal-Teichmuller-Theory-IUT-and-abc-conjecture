import tmp.sheaf.xif.paper.S750PaperRootStackOtriCarrierActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S763QPilotRootStackKummerActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S750PaperRootStackOtriCarrierActual
open LeanFormal.IUT.XiFPaper.TwoLthRootKummerActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

def qPilotScalingLog : Real :=
  ((paperRootStackOtriCarrier (l := l) T b).divisorSection
    (paperRootStackOtriCarrier (l := l) T b).qSection).toAdd *
    Real.log (qVFamTensorP T b : Real)

def thetaRootScalingLog : Real :=
  ((paperRootStackOtriCarrier (l := l) T b).divisorSection
    (paperRootStackOtriCarrier (l := l) T b).rootSection).toAdd *
    Real.log (qVFamTensorP T b : Real)

theorem qPilotScalingLog_eq_order :
    qPilotScalingLog T b =
      ((qVFamily T b).order : Real) * Real.log (qVFamTensorP T b : Real) := by
  unfold qPilotScalingLog
  rfl

theorem thetaRootScalingLog_eq_div_twoL :
    thetaRootScalingLog T b =
      (((qVFamily T b).order : Real) / (2 * l.value)) *
        Real.log (qVFamTensorP T b : Real) := by
  unfold thetaRootScalingLog
  rfl

theorem twoL_mul_thetaRootScalingLog :
    (2 * l.value : Real) * thetaRootScalingLog T b = qPilotScalingLog T b := by
  rw [thetaRootScalingLog_eq_div_twoL, qPilotScalingLog_eq_order]
  have htwo : (2 * l.value : Real) ≠ 0 := by
    exact_mod_cast Nat.mul_ne_zero (by norm_num) l.prime.ne_zero
  field_simp [htwo]

structure QPilotRootStackKummerIdentification where
  qSection : RootStackSectionCarrier T b
  rootSection : RootStackSectionCarrier T b
  root_pow : rootSection ^ (2 * l.value) = qSection
  q_divisor : Multiplicative Real
  q_divisor_eq : q_divisor = Multiplicative.ofAdd ((qVFamily T b).order : Real)
  root_divisor : Multiplicative Real
  root_divisor_eq : root_divisor =
    Multiplicative.ofAdd (((qVFamily T b).order : Real) / (2 * l.value))
  qPilotLog : Real
  qPilotLog_eq : qPilotLog =
    ((qVFamily T b).order : Real) * Real.log (qVFamTensorP T b : Real)
  rootLog : Real
  rootLog_eq : rootLog =
    (((qVFamily T b).order : Real) / (2 * l.value)) *
      Real.log (qVFamTensorP T b : Real)
  twoL_rootLog_eq_qPilotLog : (2 * l.value : Real) * rootLog = qPilotLog

noncomputable def qPilotRootStackKummerIdentification :
    QPilotRootStackKummerIdentification (l := l) T b where
  qSection := paperQSection T b
  rootSection := paperRootSection T b
  root_pow := (paperRootStackOtriCarrier (l := l) T b).root_pow
  q_divisor := Multiplicative.ofAdd ((qVFamily T b).order : Real)
  q_divisor_eq := rfl
  root_divisor := Multiplicative.ofAdd (((qVFamily T b).order : Real) / (2 * l.value))
  root_divisor_eq := rfl
  qPilotLog := qPilotScalingLog T b
  qPilotLog_eq := qPilotScalingLog_eq_order T b
  rootLog := thetaRootScalingLog T b
  rootLog_eq := thetaRootScalingLog_eq_div_twoL T b
  twoL_rootLog_eq_qPilotLog := twoL_mul_thetaRootScalingLog T b

end LeanFormal.IUT.XiFPaper.S763QPilotRootStackKummerActual
end