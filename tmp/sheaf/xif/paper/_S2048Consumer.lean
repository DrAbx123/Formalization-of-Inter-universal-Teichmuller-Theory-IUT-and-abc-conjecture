import tmp.sheaf.xif.paper.S2048TransferCompatActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2024LocalReciprocityActual
open LeanFormal.IUT.XiFPaper.S2048TransferCompatActual

namespace LeanFormal.IUT.XiFPaper.S2048Consumer

variable (p : Nat) [Fact (Nat.Prime p)]

example (r : LocalArtinTorsionMap p) (hc : ArtinTransferCompat p r) :
    LocalReciprocityData p :=
  localReciprocityDataOfArtin p r hc

example :
    localReciprocityDataMissing p ↔
      ∃ r : LocalArtinTorsionMap p, ArtinTransferCompat p r :=
  localReciprocityDataMissing_iff_artinSource p

example (e : ∀ U : Index p,
    CommGroup.torsion (Abelianization U) ≃* mu p U) :
    TransferCompat p e ↔ StageCompat p e :=
  transferCompat_iff_stage p e

end LeanFormal.IUT.XiFPaper.S2048Consumer
