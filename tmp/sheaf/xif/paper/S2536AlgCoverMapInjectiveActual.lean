import tmp.sheaf.xif.paper.S2534CoverHomMapActual

noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
open LeanFormal.IUT.XiFPaper.S2534CoverHomMapActual
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2536AlgCoverMapInjectiveActual

theorem S2536AlgCoverMap_injective {A B : CommAlgCat.FiniteEtale F} :
    Function.Injective (S2534AlgCoverMap (A := A) (B := B)) := by
  intro f g h
  have hm : (S2534AlgCoverMap f).hom.left =
      (S2534AlgCoverMap g).hom.left := by
    exact congrArg (fun m => m.hom.left) h
  change Spec.map (CommRingCat.ofHom (f.hom.hom : A.obj →+* B.obj)) =
    Spec.map (CommRingCat.ofHom (g.hom.hom : A.obj →+* B.obj)) at hm
  have hring : CommRingCat.ofHom (f.hom.hom : A.obj →+* B.obj) =
      CommRingCat.ofHom (g.hom.hom : A.obj →+* B.obj) :=
    Spec.map_inj.mp hm
  have hringhom : (f.hom.hom : A.obj →+* B.obj) =
      (g.hom.hom : A.obj →+* B.obj) :=
    congrArg (fun φ => φ.hom) hring
  have halg : f.hom.hom = g.hom.hom :=
    AlgHom.ext (fun x => congrArg (fun φ => φ x) hringhom)
  exact ObjectProperty.hom_ext (CommAlgCat.finiteEtale F) (CommAlgCat.hom_ext halg)

#check S2536AlgCoverMap_injective
#print axioms S2536AlgCoverMap_injective
end LeanFormal.IUT.XiFPaper.S2536AlgCoverMapInjectiveActual
end