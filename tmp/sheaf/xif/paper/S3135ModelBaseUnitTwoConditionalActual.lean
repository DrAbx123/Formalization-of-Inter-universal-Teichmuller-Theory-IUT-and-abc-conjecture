import tmp.sheaf.xif.paper.S3135ModelMuEqualityShapeActual

noncomputable section
open scoped BigOperators NNReal ENNReal
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.LogShellLattice
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open LeanFormal.IUT.XiFPaper.S3129IQHullLogVolumeSourceActual
open LeanFormal.IUT.XiFPaper.S3135LogShellScalarSelfSimilarityActual
open LeanFormal.IUT.XiFPaper.S3135ModelSkeletonInterfaceActual

namespace LeanFormal.IUT.XiFPaper.S3135ModelBaseUnitTwoConditionalActual

local instance measB2u : MeasurableSpace concreteLogShellField := borel _
local instance borelB2u : BorelSpace concreteLogShellField := ⟨rfl⟩

/-- **baseUnit = 2 special case (conditional)**: if the concrete rational prime
identification gives that `2` is a unit of `Z_p` and that its completion norm is one,
then the model Haar readout satisfies `mu(2*O) = mu(O)` by set equality.  This is the
special case recorded pending the `concreteRationalPrime = 5` identification; the
unconditional witness used in the reopen is `baseUnit = -1`. -/
theorem s3135_modelHaar_two_scaling_eq
    (h2u : IsUnit (2 : ℤ_[concreteRationalPrime]))
    (_h2norm : ‖algebraMap ℤ_[concreteRationalPrime] ℚ_[concreteRationalPrime]
      (2 : ℤ_[concreteRationalPrime])‖ = 1) :
    ∃ z' : ℤ_[concreteRationalPrime],
      (2 : ℤ_[concreteRationalPrime]) * z' = 1 ∧
        S3135ModelHullHaar
            ((fun x : S3135ModelHullPoint =>
                algebraMap ℚ_[concreteRationalPrime] S3135ModelHullPoint
                  ((2 : ℤ_[concreteRationalPrime]) : ℚ_[concreteRationalPrime]) * x) ''
              ((integralLogShell (K := concreteLogShellField)
                (p := concreteRationalPrime)) : Set S3135ModelHullPoint)) =
          S3135ModelHullHaar
            ((integralLogShell (K := concreteLogShellField)
              (p := concreteRationalPrime)) : Set S3135ModelHullPoint) := by
  classical
  obtain ⟨z', hz'⟩ := isUnit_iff_exists_inv.mp h2u
  refine ⟨z', hz', ?_⟩
  exact S3135ModelHaar_scaling_image_eq 2 z' hz'

#check s3135_modelHaar_two_scaling_eq
end LeanFormal.IUT.XiFPaper.S3135ModelBaseUnitTwoConditionalActual
end
