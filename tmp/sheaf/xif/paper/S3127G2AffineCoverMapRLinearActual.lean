import tmp.sheaf.xif.paper.S3127G2AffineCoverMapPreimageActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientG2
open LeanFormal.IUT.XiFPaper.S3127G2AffineCoverMapPreimageActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2AffineCoverMapRLinearActual
universe u
variable {R : Type u} [CommRing R]

theorem affineCoverMapOfAlgHom_surjective
    {B C : Type u} [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
    (hEtB : Algebra.Etale R B) (hFinB : Module.Finite R B)
    (hEtC : Algebra.Etale R C) (hFinC : Module.Finite R C)
    (u : affineCover B hEtB hFinB ⟶ affineCover C hEtC hFinC) :
    ∃ ψ : C →ₐ[R] B, u = affineCoverMapOfAlgHom hEtB hFinB hEtC hFinC ψ := by
  let ψring : C →+* B := (Spec.preimage u.hom.left).hom
  have hSpec : Spec.map (CommRingCat.ofHom ψring) = u.hom.left := by
    simpa [ψring] using affineCoverMapOfAlgHom_preimage hEtB hFinB hEtC hFinC u
  have hsq : u.hom.left ≫ Spec.map (CommRingCat.ofHom (algebraMap R C)) =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := Over.w u.hom
  have hcomp : Spec.map (CommRingCat.ofHom ψring) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R C)) =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
    rw [hSpec]
    exact hsq
  have hring : CommRingCat.ofHom (algebraMap R C) ≫ CommRingCat.ofHom ψring =
      CommRingCat.ofHom (algebraMap R B) := by
    apply Spec.map_injective
    simpa [Spec.map_comp] using hcomp
  have halg : ∀ r : R, ψring (algebraMap R C r) = algebraMap R B r := by
    intro r
    have := congrArg (fun k : CommRingCat.of R ⟶ CommRingCat.of B => k.hom r) hring
    simpa using this
  let ψ : C →ₐ[R] B := { toRingHom := ψring, commutes' := halg }
  refine ⟨ψ, ?_⟩
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  change Over.Hom.left u.hom = Spec.map (CommRingCat.ofHom ψring)
  exact hSpec.symm

#check affineCoverMapOfAlgHom_surjective
end LeanFormal.IUT.XiFPaper.S3127G2AffineCoverMapRLinearActual
end
