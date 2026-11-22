/- P6P5 control final. -/
import tmp.sheaf.xif.paper.Mzk1P6P5ThetaHullControl2
import tmp.sheaf.xif.paper.Mzk1P6P5QReadingNegM2
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P6P5ControlFinal
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1P6P5ThetaHullControl2
open LeanFormal.IUT.XiFPaper.Mzk1P6P5QReadingNegM2
variable {l : PrimeGeFive} (X : N8NativeInput l)
variable [Fintype (Bad (nativePlaceSelection X.S))]
theorem control_final (M : Real) :
    qPilotRealifiedLogVolume X = -M → M = paperQFromM (l := l) M / (2 * (l.value : Real)) := by
  intro h
  exact M_eq_Q_div_two_l M
#check control_final
end LeanFormal.IUT.XiFPaper.Mzk1P6P5ControlFinal
end
