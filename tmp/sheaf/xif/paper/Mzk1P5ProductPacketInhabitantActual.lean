import tmp.sheaf.xif.paper.Mzk1P5PacketTableActual
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorFieldDecomposition
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P5ProductPacketInhabitantActual
/-- The product decomposition donor exists: `J`, `E`, algebra equivalence `e`.
It provides no actual Haar reference lattice `C_t` and no finite source image `G_t`. -/
def productPacketDonors : List String :=
  [ "FinitePadicTensorFieldDecomposition.exists_finiteNormedFieldProduct_piTensor",
    "Mzk1P5PacketTableActual.PacketFourColumnTable",
    "Mzk1P5TensorUltrametricActual.finitePadicTensor_isUltrametric" ]
theorem productPacketDonors_length : productPacketDonors.length = 3 := rfl
/-- Exact missing inhabitant: the actual packet datum with a genuine Haar
reference lattice and a nonzero finite source column set.  No inhabitant is
asserted. -/
structure MissingProductPacketData where
  hasHaarReferenceLattice : Prop
  hasFiniteSourceImage : Prop
  rootEquation : Prop
#check MissingProductPacketData
end LeanFormal.IUT.XiFPaper.Mzk1P5ProductPacketInhabitantActual
end