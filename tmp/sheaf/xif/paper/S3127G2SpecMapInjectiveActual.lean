import tmp.sheaf.xif.paper.S3127KLinearFullActual
import tmp.sheaf.xif.paper.S3127FreeQuotientActual
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2SpecMapInjectiveActual
universe u
variable {R : Type u} [CommRing R]

theorem affineCoverMapOfAlgHom_injective
    {B C : Type u} [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
    [Algebra.Etale R B] [Algebra.Etale R C]
    [Module.Finite R B] [Module.Finite R C]
    (ψ ψ' : B →ₐ[R] C)
    (h : affineCoverMapOfAlgHom (R := R) (A := B) (B := C)
      inferInstance inferInstance inferInstance inferInstance ψ =
      affineCoverMapOfAlgHom (R := R) (A := B) (B := C)
      inferInstance inferInstance inferInstance inferInstance ψ') :
    ψ = ψ' := by
  have hraw : Spec.map (CommRingCat.ofHom (ψ : B →+* C)) =
      Spec.map (CommRingCat.ofHom (ψ' : B →+* C)) := by
    simpa [affineCoverMapOfAlgHom] using congrArg (fun k => k.hom.left) h
  have hring : CommRingCat.ofHom (ψ : B →+* C) =
      CommRingCat.ofHom (ψ' : B →+* C) := Spec.map_injective hraw
  have hfun : (ψ : B →+* C) = (ψ' : B →+* C) :=
    congrArg CommRingCat.Hom.hom hring
  exact AlgHom.ext (fun b => congrFun (congrArg DFunLike.coe hfun) b)

#check affineCoverMapOfAlgHom_injective
end LeanFormal.IUT.XiFPaper.S3127G2SpecMapInjectiveActual
end
