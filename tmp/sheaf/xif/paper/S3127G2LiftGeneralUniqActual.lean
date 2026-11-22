import tmp.sheaf.xif.paper.S3127G2AffineQuotientCoverMapCompActual
import tmp.sheaf.xif.paper.S3127GammaActionActual
import tmp.sheaf.xif.paper.S3127G2AffineCoverMapRLinearActual
import tmp.sheaf.xif.paper.S3127G2QFullAffineCoverEqActual
import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleFixedPointsGeneral
import LeanFormal.IUT.Foundations.AlgebraicGeometry.InvariantsGeneralAssembly
import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientG2
open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
open LeanFormal.IUT.XiFPaper.S3127G2AffineQuotientCoverMapCompActual
open LeanFormal.IUT.XiFPaper.S3127G2AffineCoverMapRLinearActual
open LeanFormal.IUT.XiFPaper.S3127G2QFullAffineCoverEqActual
open LeanFormal.IUT.XiFPaper.S3127GammaActionActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2LiftGeneralUniqActual
universe u
variable {R : Type u} [CommRing R]
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
variable {G : Type u} [Group G] [Fintype G] [DecidableEq G]
variable [MulSemiringAction G A] [SMulCommClass G R A]
variable [Algebra.Etale R A] [Module.Finite R A]
variable (hEtA : Algebra.Etale R A) (hFinA : Module.Finite R A)
variable (hEtB : Algebra.Etale R B) (hFinB : Module.Finite R B)
variable (φ : B →ₐ[R] A)
variable (hφ : ∀ (g : G) (b : B), groupActionRingEquiv A G g (φ b) = φ b)

theorem affineQuotientCoverLiftGeneral_uniq
    (u : affineQuotientCoverGeneral (R := R) A G ⟶ affineCover B hEtB hFinB)
    (hu : affineQuotientCoverMapGeneral (R := R) A G ≫ u =
      affineCoverMapOfAlgHom
        hEtA
        hFinA hEtB hFinB φ) :
    u = affineQuotientCoverLiftGeneral hEtB hFinB φ hφ := by
  let hFix : Algebra.Etale R (fixedPointSubalgebra R A G) ∧
      Module.Finite R (fixedPointSubalgebra R A G) :=
    FiniteEtaleFixedPointsGeneral.fixedPointSubalgebra_finiteEtale
      (R := R) (A := A) (G := G)
  haveI : Algebra.Etale R (fixedPointSubalgebra R A G) := hFix.1
  haveI : Module.Finite R (fixedPointSubalgebra R A G) := hFix.2
  obtain ⟨ψ0, hψ0, huniq⟩ := ABCBridge.InvariantsGeneralAssembly.affineFixedPointQuotient_universal R A G φ hφ
  have canonical : ∀ (v : affineQuotientCoverGeneral (R := R) A G ⟶
      affineCover B hEtB hFinB),
      affineQuotientCoverMapGeneral (R := R) A G ≫ v =
        affineCoverMapOfAlgHom
          hEtA
          hFinA hEtB hFinB φ →
      v = affineCoverMapOfAlgHom hFix.1 hFix.2 hEtB hFinB ψ0 := by
    intro v hv
    let v' : affineCover (fixedPointSubalgebra R A G) hFix.1 hFix.2 ⟶
        affineCover B hEtB hFinB := v
    have hv' : affineQuotientCoverMapGeneral (R := R) A G ≫ v' =
        affineCoverMapOfAlgHom hEtA hFinA hEtB hFinB φ := by
      simpa [v'] using hv
    obtain ⟨ψv, hψv⟩ :=
      affineCoverMapOfAlgHom_surjective hFix.1 hFix.2 hEtB hFinB v'
    have hOver : affineCoverMapOfAlgHom hEtA hFinA hEtB hFinB
        ((Subalgebra.val (fixedPointSubalgebra R A G)).comp ψv) =
        affineCoverMapOfAlgHom hEtA hFinA hEtB hFinB φ := by
      calc
        affineCoverMapOfAlgHom hEtA hFinA hEtB hFinB
            ((Subalgebra.val (fixedPointSubalgebra R A G)).comp ψv) =
            affineQuotientCoverMapGeneral (R := R) A G ≫
              affineCoverMapOfAlgHom hFix.1 hFix.2 hEtB hFinB ψv := by
          exact (affineQuotientCoverMapGeneral_comp hEtB hFinB ψv).symm
        _ = affineQuotientCoverMapGeneral (R := R) A G ≫ v' := by
          rw [hψv]
        _ = affineCoverMapOfAlgHom hEtA hFinA hEtB hFinB φ := hv'
    have hring : ((Subalgebra.val (fixedPointSubalgebra R A G)).comp ψv :
        B →+* A) = (φ : B →+* A) := by
      have h : Spec.map (CommRingCat.ofHom
          (((Subalgebra.val (fixedPointSubalgebra R A G)).comp ψv :
            B →ₐ[R] A) : B →+* A)) =
          Spec.map (CommRingCat.ofHom (φ : B →+* A)) := by
        have h' := congrArg (fun k => k.hom.left) hOver
        change Spec.map (CommRingCat.ofHom
          (((Subalgebra.val (fixedPointSubalgebra R A G)).comp ψv :
            B →ₐ[R] A) : B →+* A)) =
          Spec.map (CommRingCat.ofHom (φ : B →+* A)) at h'
        exact h'
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)
    have hval : (fixedPointInclusion R A G).comp ψv = φ := by
      apply AlgHom.ext
      intro b
      exact congrArg (fun f : B →+* A => f b) hring
    have hψeq : ψv = ψ0 := huniq ψv hval
    rw [hψeq] at hψv
    simpa [v', S3127G2QFullAffineCoverEq] using hψv
  have hu' := canonical u hu
  have hl' := canonical
    (affineQuotientCoverLiftGeneral hEtB hFinB φ hφ)
    (affineQuotientCoverLiftGeneral_fac hEtB hFinB φ hφ)
  exact hu'.trans hl'.symm

#check affineQuotientCoverLiftGeneral_uniq
end LeanFormal.IUT.XiFPaper.S3127G2LiftGeneralUniqActual
end
