import tmp.sheaf.xif.paper.S2098M2aCoreActual

noncomputable section
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2024LocalReciprocityActual
open LeanFormal.IUT.XiFPaper.S2098M2aCoreActual

namespace LeanFormal.IUT.XiFPaper.S2098Consumer

variable {p : Nat} [Fact (Nat.Prime p)]
variable (U : Index p)

#check @LeanFormal.IUT.XiFPaper.S2098M2aCoreActual.localReciprocityIsomorphism_holds
#check @LeanFormal.IUT.XiFPaper.S2098M2aCoreActual.localArtinTorsion_holds
#check @LeanFormal.IUT.XiFPaper.S2098M2aCoreActual.localArtinSourceArtin
#check @LeanFormal.IUT.XiFPaper.S2098M2aCoreActual.unitProfiniteCompletionEquivGal_eta
#check @LeanFormal.IUT.XiFPaper.S2098M2aCoreActual.localReciprocityData_of_source
#check @LeanFormal.IUT.XiFPaper.S2098M2aCoreActual.muHatComparison_of_source

example : localReciprocityIsomorphism p U := localReciprocityIsomorphism_holds U
example : localArtinTorsion p U := localArtinTorsion_holds U
example : Nonempty (unitProfiniteCompletion p U ≃*
    Gal(↥(maximalAbelianExtension p U) / localField p U)) :=
  ⟨unitProfiniteCompletionEquivGal U⟩
example (hc : localArtinSourceCarrierMissing (p := p))
    (htransfer : localReciprocityTransferCompatibility hc) :
    Nonempty (LocalReciprocityData p) :=
  ⟨localReciprocityData_of_source hc htransfer⟩
example (hc : localArtinSourceCarrierMissing (p := p))
    (htransfer : localReciprocityTransferCompatibility hc) :
    muHatComparison p :=
  muHatComparison_of_source hc htransfer

end LeanFormal.IUT.XiFPaper.S2098Consumer
