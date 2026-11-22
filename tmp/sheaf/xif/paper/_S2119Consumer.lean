import tmp.sheaf.xif.paper.S2119VerCarrierActual

noncomputable section
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2113M2bTransferActual
open LeanFormal.IUT.XiFPaper.S2119VerCarrierActual

namespace Consumer

variable {p : Nat} [Fact (Nat.Prime p)]

example : VerCarrierComparison (p := p) :=
  verCarrierComparison (p := p)

example {H K : Index p} (h : H ≤ K) :
    Nonempty (Gal(↥(PadicField.maxAbelian (↥(K' (p := p) h)) (AlgebraicClosure ℚ_[p])) / ↥(K' (p := p) h)) ≃*
      Gal(↥(maximalAbelianExtension p H) / localField p H)) :=
  verCarrierComparison_K' (p := p) h

#check verS2027
#check artinTransfer_S2027
#check M2bFirstMissing

end Consumer

end
