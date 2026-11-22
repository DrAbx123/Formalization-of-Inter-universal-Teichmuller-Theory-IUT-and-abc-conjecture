import tmp.sheaf.xif.paper.S3135ModelScalingPairActual
import tmp.sheaf.xif.paper.S3135ModelValueUnitActual
import tmp.sheaf.xif.paper.S3135ModelMuEqualityShapeActual
import LeanFormal.IUT.IUTII.Frobenioid.ConcreteSourceFrobenioidBridge
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlacePadicScalarStructure

noncomputable section
open scoped BigOperators NNReal ENNReal
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.LogShellLattice
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open LeanFormal.IUT.XiFPaper.S3129IQHullLogVolumeSourceActual
open LeanFormal.IUT.XiFPaper.S3135LogShellScalarSelfSimilarityActual
open LeanFormal.IUT.XiFPaper.S3135ModelSkeletonInterfaceActual
open LeanFormal.IUT.XiFPaper.S3135ModelScalingBatchActual
open LeanFormal.IUT.XiFPaper.S3135ModelValueUnitBatchActual
open LeanFormal.IUT.XiFPaper.S3135ModelBatch3Actual
open LeanFormal.IUT.XiFPaper.S3135ModelValueDataActual
open LeanFormal.IUT.XiFPaper.S3135ModelValueDataUnitFactorActual
open LeanFormal.IUT.XiFPaper.S3135ModelBatch3Actual


local instance factBaseCRP : Fact (Nat.Prime concreteRationalPrime) :=
  LeanFormal.IUT.NumberFieldFinitePlace.completionRationalPrime_fact concretePlace

namespace LeanFormal.IUT.XiFPaper.S3135ModelBaseUnitActualAdapted

local instance measBU : MeasurableSpace concreteLogShellField := borel _
local instance borelBU : BorelSpace concreteLogShellField := ⟨rfl⟩

/-- The completion-side base unit `-1` of the model scaling (a genuine nontrivial unit
of norm one: `(-1)*(-1)=1`, `||-1|| = 1`). -/
noncomputable def s3135_modelBaseUnit : ℚ_[concreteRationalPrime]ˣ where
  val := (-1 : ℚ_[concreteRationalPrime])
  inv := (-1 : ℚ_[concreteRationalPrime])
  val_inv := by ring
  inv_val := by ring

/-- The base unit has norm one. -/
theorem s3135_modelBaseUnit_norm_one :
    ‖(s3135_modelBaseUnit : ℚ_[concreteRationalPrime])‖ = 1 := by
  show ‖(-1 : ℚ_[concreteRationalPrime])‖ = 1
  rw [norm_neg, norm_one]

/-- The corresponding `Z_p`-unit scalar pair `(-1, -1)` has product one. -/
theorem s3135_zp_negOne_mul :
    (-1 : ℤ_[concreteRationalPrime]) * (-1 : ℤ_[concreteRationalPrime]) = 1 := by
  ring

/-- **μ(2·O)=μ(O) instance at a genuine nontrivial unit**: the actual Haar readout of
the scaled integral log-shell by the `Z_p`-unit `-1` equals that of the integral
log-shell. -/
theorem s3135_modelHaar_negOne_scaling_eq :
    S3135ModelHullHaar
        ((fun x : S3135ModelHullPoint =>
            algebraMap ℚ_[concreteRationalPrime] S3135ModelHullPoint
              ((-1 : ℤ_[concreteRationalPrime]) : ℚ_[concreteRationalPrime]) * x) ''
          ((integralLogShell (K := concreteLogShellField)
            (p := concreteRationalPrime)) : Set S3135ModelHullPoint)) =
      S3135ModelHullHaar
        ((integralLogShell (K := concreteLogShellField)
          (p := concreteRationalPrime)) : Set S3135ModelHullPoint) :=
  S3135ModelHaar_scaling_image_eq (-1) (-1) s3135_zp_negOne_mul

#check s3135_modelBaseUnit
#check s3135_modelBaseUnit_norm_one
#check s3135_zp_negOne_mul
#check s3135_modelHaar_negOne_scaling_eq

end LeanFormal.IUT.XiFPaper.S3135ModelBaseUnitActualAdapted
end