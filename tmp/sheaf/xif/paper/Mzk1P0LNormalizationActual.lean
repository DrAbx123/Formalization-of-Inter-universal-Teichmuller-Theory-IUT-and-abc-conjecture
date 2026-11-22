import tmp.sheaf.xif.paper.Mzk1P0LPaperInstanceActual
import tmp.sheaf.xif.paper.S1915ThetaHullA0Actual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0LNormalizationActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.Mzk1P0LPaperInstanceActual
variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)
noncomputable def lThetaNormFactor : Real :=
  thetaReadActual I place - Real.log ‖(C3LAt I place).q.q‖
theorem lThetaNormFactor_eq :
    lThetaNormFactor I place =
      thetaReadActual I place - Real.log ‖(C3LAt I place).q.q‖ := rfl
def lThetaNormalizationGap : Prop :=
  thetaReadActual I place = Real.log ‖(C3LAt I place).q.q‖
structure LThetaNormalizationData where
  factor : Real
  factor_eq : factor = thetaReadActual I place - Real.log ‖(C3LAt I place).q.q‖
def LThetaNormalizationData_nonempty : Prop := Nonempty (LThetaNormalizationData I place)
end LeanFormal.IUT.XiFPaper.Mzk1P0LNormalizationActual