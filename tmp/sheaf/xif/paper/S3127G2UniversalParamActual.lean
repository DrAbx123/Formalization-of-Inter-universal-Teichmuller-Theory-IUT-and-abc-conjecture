import tmp.sheaf.xif.paper.S3127G2QuotientMapActual
import tmp.sheaf.xif.paper.S3127FullForgetActual
import tmp.sheaf.xif.paper.S3127G2ActionBaseActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
open LeanFormal.IUT.XiFPaper.S3127G2CoverIsoActual
open LeanFormal.IUT.XiFPaper.S3127G2QuotientMapActualFull
open LeanFormal.IUT.XiFPaper.S3127FullForgetActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
namespace LeanFormal.IUT.XiFPaper.S3127G2UniversalParamActual
variable {l : PrimeGeFive} {G : Type} [Group G]

theorem S3127G2Universal_of_phi
    (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G)
    (Qobj : S3127FiniteEtaleOverKFull l)
    (q : A ⟶ Qobj)
    (phi : forall {B : S3127FiniteEtaleOverKFull l} (f : A ⟶ B),
      (forall g : G, S3127G2Action A act g ≫ f = f) -> Prop)
    (hphi : forall {B : S3127FiniteEtaleOverKFull l} (f : A ⟶ B)
      (hinv : forall g : G, S3127G2Action A act g ≫ f = f), phi f hinv)
    (hfac : forall {B : S3127FiniteEtaleOverKFull l} (f : A ⟶ B)
      (hinv : forall g : G, S3127G2Action A act g ≫ f = f),
      ∃! v_raw : S3127FullForget.obj Qobj ⟶ S3127FullForget.obj B,
        S3127FullForget.map q ≫ v_raw = S3127FullForget.map f) :
    forall {B : S3127FiniteEtaleOverKFull l} (f : A ⟶ B),
      (forall g : G, S3127G2Action A act g ≫ f = f) ->
      ∃! v : Qobj ⟶ B, q ≫ v = f := by
  intro B f hinv
  obtain ⟨v_raw, hv_raw, huniq⟩ := hfac f hinv
  let v : Qobj ⟶ B := S3127FullForget.preimage v_raw
  have hmap : S3127FullForget.map v = v_raw := S3127FullForget.map_preimage v_raw
  refine ⟨v, ?_, ?_⟩
  · apply (S3127FullForget_faithful (l := l)).map_injective
    rw [S3127FullForget.map_comp, hmap, hv_raw]
  · intro v' hv'
    apply (S3127FullForget_faithful (l := l)).map_injective
    have hv'' : S3127FullForget.map q ≫ S3127FullForget.map v' =
        S3127FullForget.map f := by
      rw [← S3127FullForget.map_comp, hv']
    have hv_raw' : S3127FullForget.map q ≫ S3127FullForget.map v =
        S3127FullForget.map f := by
      rw [hmap, hv_raw]
    calc
      S3127FullForget.map v' = v_raw := huniq _ hv''
      _ = S3127FullForget.map v := (huniq _ hv_raw').symm

#check S3127G2Universal_of_phi
end LeanFormal.IUT.XiFPaper.S3127G2UniversalParamActual
end