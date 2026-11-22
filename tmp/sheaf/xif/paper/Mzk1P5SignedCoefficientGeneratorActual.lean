import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceStepVAssembly
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual

namespace LeanFormal.IUT.XiFPaper.Mzk1P5SignedCoefficientGeneratorActual

variable {p : Nat} [Fact p.Prime] {ι : Type} [Fintype ι]
variable {K : Type*} [Field K] [NumberField K]
variable {V : ι → Type*}
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
variable (tuple : (i : ι) → V i)

/-- Negative of a positive-coefficient pure fractional scaling datum: invert the
actual local generators and instantiate the exact generator constructor at `-c`. -/
noncomputable def arithmeticTuplePureFractionalScalingData_neg
    {c : ι → Real} (data : ArithmeticTuplePureFractionalScalingData places tuple c) :
    ArithmeticTuplePureFractionalScalingData places tuple (fun i => -c i) :=
  arithmeticTuplePureFractionalScalingData_ofGenerator places tuple
    (fun i => -c i) (fun i => (data.localGenerator i)⁻¹) (fun i => by
      rw [norm_inv, data.localGenerator_norm]
      rw [show (p : Real) ^ (-(-c i)) = ((p : Real) ^ (-c i))⁻¹ by
        rw [Real.rpow_neg]; ring]
      exact inv_inv _ ▸ rfl)

/-- The normalized qVFam generator inverted gives actual scaling data at the
negative normalized coefficient. -/
noncomputable def qVFamNormalizedNegScalingData
    {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T)) :
    ArithmeticTuplePureFractionalScalingData
      (qVFamTensorPlaces T b) qVFamTensorTuple
      (fun i => -qVFamNormalizedCoefficientFamily T b i) :=
  arithmeticTuplePureFractionalScalingData_neg
    (qVFamTensorPlaces T b) qVFamTensorTuple
    (qVFamNormalizedPureFractionalScalingData T b)

#print axioms arithmeticTuplePureFractionalScalingData_neg

end LeanFormal.IUT.XiFPaper.Mzk1P5SignedCoefficientGeneratorActual
end