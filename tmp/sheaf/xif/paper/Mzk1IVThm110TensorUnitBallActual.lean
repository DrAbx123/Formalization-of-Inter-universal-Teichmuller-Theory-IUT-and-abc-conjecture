import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorFieldDecomposition
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1IVThm110TensorUnitBallActual
/-- The tensor unit ball requires a contractive/isometric comparison of the
finite field product decomposition. The algebraic decomposition donor
`exists_finiteNormedFieldProduct_piTensor` provides only an algebra equivalence
and continuity, not a norm comparison, so the tensor unit ball is not proved
here. -/
def missingTensorUnitBallDonors : List String :=
  [ "isometry or contractive norm comparison for the product decomposition",
    "coordinatewise norm ≤ 1 on the decomposed tensor log shell" ]
theorem missingTensorUnitBallDonors_length :
    missingTensorUnitBallDonors.length = 2 := rfl
#check missingTensorUnitBallDonors
end LeanFormal.IUT.XiFPaper.Mzk1IVThm110TensorUnitBallActual
end