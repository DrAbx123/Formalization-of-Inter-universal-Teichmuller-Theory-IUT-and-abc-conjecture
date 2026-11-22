import tmp.sheaf.xif.paper.S3119NegInvolutionOverActual
import tmp.sheaf.xif.paper.S1419AutoProbe
noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped SpecOfNotation
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3119NegInvolutionAttempt
open LeanFormal.IUT.XiFPaper.S3119NegInvolutionOverActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
namespace LeanFormal.IUT.XiFPaper.S3119OverAutoAlgEquivProbeAdapted
set_option backward.isDefEq.respectTransparency false

variable {l : PrimeGeFive}

/-- The K-algebra automorphism underlying an Over automorphism, written via
Spec.map_surjective. -/
noncomputable def S3119AlgHomOfOverAuto
    (β : S1419AffineOver (l := l) ⟶ S1419AffineOver (l := l)) :
    S1348CoordinateRing l →ₐ[S1348K l] S1348CoordinateRing l := by
  classical
  let g0 : CommRingCat.of (S1348CoordinateRing l) ⟶
      CommRingCat.of (S1348CoordinateRing l) :=
    Classical.choose (Spec.map_surjective β.left)
  have hg0 : Spec.map g0 = β.left :=
    Classical.choose_spec (Spec.map_surjective β.left)
  let f0 : S1348CoordinateRing l →+* S1348CoordinateRing l := g0.hom
  have hf0 : (β.left : Spec (CommRingCat.of (S1348CoordinateRing l)) ⟶
      Spec (CommRingCat.of (S1348CoordinateRing l))) =
      Spec.map (CommRingCat.ofHom f0) := hg0.symm
  have hcomm : f0.comp (algebraMap (S1348K l) (S1348CoordinateRing l)) =
      algebraMap (S1348K l) (S1348CoordinateRing l) := by
    have hw := Over.w β
    rw [hf0] at hw
    have hSpec : Spec.map (CommRingCat.ofHom
        (f0.comp (algebraMap (S1348K l) (S1348CoordinateRing l)))) =
        Spec.map (CommRingCat.ofHom
          (algebraMap (S1348K l) (S1348CoordinateRing l))) := by
      rw [show CommRingCat.ofHom
          (f0.comp (algebraMap (S1348K l) (S1348CoordinateRing l))) =
          CommRingCat.ofHom (algebraMap (S1348K l) (S1348CoordinateRing l)) ≫
            CommRingCat.ofHom f0 from rfl]
      rw [Spec.map_comp]
      exact hw
    have hcat := Spec.map_injective hSpec
    exact congrArg CommRingCat.Hom.hom hcat
  exact { toRingHom := f0, commutes' := fun x => RingHom.congr_fun hcomm x }

#check S3119AlgHomOfOverAuto
end LeanFormal.IUT.XiFPaper.S3119OverAutoAlgEquivProbeAdapted
end
