import tmp.sheaf.xif.paper.S3127KLinearFullActual
import tmp.sheaf.xif.paper.S3127FreeQuotientActual
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientG2
import LeanFormal.IUT.IUTII.Frobenioid.Example36EtaleCoverFoundations
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientG2
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2AffineCoverMapPreimageActual
universe u
variable {R : Type u} [CommRing R]

theorem affineCoverMapOfAlgHom_preimage
    {B C : Type u} [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
    (hEtB : Algebra.Etale R B) (hFinB : Module.Finite R B)
    (hEtC : Algebra.Etale R C) (hFinC : Module.Finite R C)
    (u : affineCover B hEtB hFinB ⟶ affineCover C hEtC hFinC) :
    let ψring : C →+* B := (Spec.preimage u.hom.left).hom
    Spec.map (CommRingCat.ofHom ψring) = u.hom.left := by
  let ψring : C →+* B := (Spec.preimage u.hom.left).hom
  change Spec.map (CommRingCat.ofHom ψring) = u.hom.left
  simpa [ψring] using Spec.map_preimage u.hom.left

#check affineCoverMapOfAlgHom_preimage
end LeanFormal.IUT.XiFPaper.S3127G2AffineCoverMapPreimageActual
end
