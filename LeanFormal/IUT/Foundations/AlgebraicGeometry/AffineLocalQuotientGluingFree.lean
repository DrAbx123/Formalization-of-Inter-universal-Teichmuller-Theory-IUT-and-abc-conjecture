import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineLocalQuotientGluingConstruct
import LeanFormal.IUT.Foundations.AlgebraicGeometry.PermutationTorsorQuotient
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Morphisms.Etale

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option relaxedAutoImplicit false

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineLocalQuotientGluingFree

noncomputable section

universe u

open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineLocalQuotientGluingConstruct
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

/-- Kummer's free-torsor orbit chart: for a transitive permutation action, the
fixed subalgebra of `ι → R` is the base `R`. -/
noncomputable def freeOrbitFixedPointsEquiv (R : Type u) [CommRing R]
    (G : Type u) [Group G] [Nonempty G] :
    FixedPoints.subalgebra R (G → R) G ≃ₐ[R] R :=
  PermutationTorsorQuotient.regular_fixedPoints_equiv (R := R) (G := G)

/-- The trivialized free-torsor cover of an affine open cover `𝒰 : S.OpenCover`:
the local quotient charts are the affine opens themselves. -/
noncomputable def freeTorsorPreglueData {S : Scheme.{u}} (𝒰 : S.OpenCover.{u}) :
    AffineLocalQuotientPreglueData S :=
  let D := 𝒰.gluedCover
  { J := D.J
    U := D.U
    V := D.V
    f := D.f
    f_open := D.f_open
    f_hasPullback := D.f_hasPullback
    f_id := D.f_id
    t := D.t
    t_id := D.t_id
    t' := D.t'
    t_fac := D.t_fac
    cocycle := D.cocycle
    q := fun i => 𝒰.f i
    q_etale := fun i => by
      change Etale (𝒰.f i)
      infer_instance }

lemma freeTorsor_toSchemeGlueData_eq {S : Scheme.{u}} (𝒰 : S.OpenCover.{u}) :
    (freeTorsorPreglueData 𝒰).toSchemeGlueData = 𝒰.gluedCover := rfl

noncomputable def freeTorsorGluedIso {S : Scheme.{u}} (𝒰 : S.OpenCover.{u}) :
    (freeTorsorPreglueData 𝒰).toSchemeGlueData.glued ≅ S := by
  rw [freeTorsor_toSchemeGlueData_eq 𝒰]
  exact asIso 𝒰.fromGlued

noncomputable def freeTorsorFiniteEtaleCover {S : Scheme.{u}} (𝒰 : S.OpenCover.{u}) :
    FiniteEtaleCover S :=
  FiniteEtaleCover.mk (freeTorsorGluedIso 𝒰).hom (by infer_instance) (by infer_instance)


theorem freeTorsorGluedMap_etale {S : Scheme.{u}} (𝒰 : S.OpenCover.{u}) :
    Etale (freeTorsorGluedIso 𝒰).hom := by
  infer_instance

theorem freeTorsorGluedMap_finite {S : Scheme.{u}} (𝒰 : S.OpenCover.{u}) :
    IsFinite (freeTorsorGluedIso 𝒰).hom := by
  infer_instance

theorem freeTorsorCover_isFiniteEtale {S : Scheme.{u}} (𝒰 : S.OpenCover.{u}) :
    IsFiniteEtaleHom (freeTorsorFiniteEtaleCover 𝒰).structureMap := by
  exact ⟨(freeTorsorFiniteEtaleCover 𝒰).etale_structureMap,
    (freeTorsorFiniteEtaleCover 𝒰).finite_structureMap⟩

end
end LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineLocalQuotientGluingFree