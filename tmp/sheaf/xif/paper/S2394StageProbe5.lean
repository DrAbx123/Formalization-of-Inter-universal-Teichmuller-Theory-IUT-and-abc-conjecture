import tmp.sheaf.xif.paper.S2200TransferNaturalityActual
import tmp.sheaf.xif.paper.S2179StageConjEquivActual

noncomputable section
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2169MuQZConjugationActual
open LeanFormal.IUT.XiFPaper.S2173StageConjugationActual
open LeanFormal.IUT.XiFPaper.S2179StageConjEquivActual
open LeanFormal.IUT.XiFPaper.S2200TransferNaturalityActual

namespace TestStage5
variable (p : Nat) [Fact (Nat.Prime p)]

example (g : Gv p) (H : Index p)
    (h : H.toSubgroup.map (MulAut.conj g.symm).toMonoidHom =
      H.toSubgroup.comap (MulAut.conj g).toMonoidHom) :
    (let e : ↥H ≃* ↥(H.toSubgroup.map (MulAut.conj g.symm).toMonoidHom) :=
      Subgroup.equivMapOfInjective H.toSubgroup
        (MulAut.conj g.symm).toMonoidHom (MulAut.conj g.symm).injective
     h ▸ e) =
    (let e : ↥H ≃* ↥(H.toSubgroup.map (MulAut.conj g.symm).toMonoidHom) :=
      Subgroup.equivMapOfInjective H.toSubgroup
        (MulAut.conj g.symm).toMonoidHom (MulAut.conj g.symm).injective
     e.trans (MulEquiv.subgroupCongr h)) := by
  dsimp only
  ext x
  change ((Subgroup.equivMapOfInjective H.toSubgroup
      (MulAut.conj g.symm).toMonoidHom (MulAut.conj g.symm).injective) x : Gv p) =
    ((Subgroup.equivMapOfInjective H.toSubgroup
      (MulAut.conj g.symm).toMonoidHom (MulAut.conj g.symm).injective) x : Gv p)
  rfl

end TestStage5
