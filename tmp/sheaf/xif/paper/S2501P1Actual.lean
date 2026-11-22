import tmp.sheaf.xif.paper.S2495cFUnconditionalActual
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import tmp.sheaf.xif.paper.S2199RepresentableStackActual

noncomputable section
open AlgebraicGeometry CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2490RestrictionSectionActual
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2501P1Actual

abbrev S2501Grading : ℕ → Submodule S2490A.K (MvPolynomial (Fin 2) S2490A.K) :=
  MvPolynomial.homogeneousSubmodule (Fin 2) S2490A.K

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable abbrev S2501P1 : Scheme :=
  AlgebraicGeometry.Proj S2501Grading

noncomputable def S2501Open : Scheme :=
  Spec (CommRingCat.of (HomogeneousLocalization.Away S2501Grading (MvPolynomial.X 1)))

noncomputable def S2501OpenMap :
    S2501Open ⟶ S2501P1 :=
  AlgebraicGeometry.Proj.awayι S2501Grading (MvPolynomial.X 1)
    (by
      rw [MvPolynomial.mem_homogeneousSubmodule]
      exact MvPolynomial.isHomogeneous_X S2490A.K 1)
    (by norm_num)

instance : IsOpenImmersion S2501OpenMap := by
  change IsOpenImmersion
    (AlgebraicGeometry.Proj.awayι S2501Grading (MvPolynomial.X 1) _ _)
  infer_instance

#check S2501OpenMap

#check GradedRing.projZeroRingHom'
#check AlgebraicGeometry.Proj.toSpecZero

noncomputable def S2501P1Over : Iut.SchemeOverField S2490A.K :=
  Over.mk (AlgebraicGeometry.Proj.toSpecZero S2501Grading ≫
    Spec.map (CommRingCat.ofHom
      ((GradedRing.projZeroRingHom' S2501Grading).comp
        (MvPolynomial.C : S2490A.K →+* MvPolynomial (Fin 2) S2490A.K))))

#check S2501P1Over

noncomputable def S2501P1Stack : Iut.EtaleStackOverField S2490A.K :=
  { fiber := Iut.schemeRepresentableEtalePseudofunctor S2490A.K S2501P1Over
    isStack := LeanFormal.IUT.XiFPaper.S2199RepresentableStackActual.s2199_representable_isStack S2490A.K S2501P1Over }

end LeanFormal.IUT.XiFPaper.S2501P1Actual
end