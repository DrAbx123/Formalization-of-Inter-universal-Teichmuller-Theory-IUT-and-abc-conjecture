/- kurt 的 norm-order 桥 (1): urCeilData 的 localGenerator 的 localNormOrder = urCeilC。
   donor: Mzk1URThetaHullLowerActual.{urCeilC, urCeilGenerator, urCeilGenerator_norm, urCeilData}（DONE）;
   LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceStepVAssembly.localNormOrder_eq_of_norm_eq_rpow
   （`‖x‖ = p^(-a) ⇒ localNormOrder p x = a`）。 -/
import tmp.sheaf.xif.paper.Mzk1URThetaHullLowerActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceStepVAssembly
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1URNormOrderBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaHullLowerActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- (1) `localNormOrder p ((urCeilData T b).localGenerator ()) = urCeilC T b`。 -/
theorem urCeilData_localGenerator_normOrder (b : Bad (nativePlaceSelection T)) :
    LocalFieldLogarithm.localNormOrder (qVFamTensorP T b)
      ((urCeilData (l := l) T b).localGenerator ()) = urCeilC (l := l) T b := by
  have hg : (urCeilData (l := l) T b).localGenerator () = urCeilGenerator (l := l) T b :=
    rfl
  rw [hg]
  exact LocalFieldLogarithm.localNormOrder_eq_of_norm_eq_rpow
    (urCeilGenerator_norm (l := l) T b)

#print axioms urCeilData_localGenerator_normOrder

end LeanFormal.IUT.XiFPaper.Mzk1URNormOrderBridgeActual