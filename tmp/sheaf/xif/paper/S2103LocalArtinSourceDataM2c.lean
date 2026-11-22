import tmp.sheaf.xif.paper.S2102TorsionArtinActual
import tmp.sheaf.xif.paper.S2046M2S2089Port
noncomputable section
set_option maxHeartbeats 2000000
namespace LeanFormal.IUT.XiFPaper.S2103LocalArtinSourceDataM2c
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2102TorsionArtinActual
open LeanFormal.IUT.XiFPaper.S2046M2S2089Port
variable {p : Nat} [Fact (Nat.Prime p)]
/-- M2c: exact remaining carrier comparison on torsion. -/
abbrev CarrierComparison (U : LeanFormal.IUT.XiFPaper.S2017VerlagerungActual.Index p) : Type :=
  CommGroup.torsion (Abelianization ↥U) ≃*
    CommGroup.torsion (TopologicalAbelianization (localGaloisGroup p U))
/-- With M2a actual from S2102 and the M2c carrier comparison, the S2027
LocalArtinSourceData inhabitant exists. -/
noncomputable def localArtinSourceDataOfCarrier
    (hC : ∀ U, CarrierComparison (p := p) U) : LocalArtinSourceData p where
  artin := fun U => S2046M2TorsionRequired_actual U
  carrier := hC
#print axioms localArtinSourceDataOfCarrier
end LeanFormal.IUT.XiFPaper.S2103LocalArtinSourceDataM2c
end
