import tmp.sheaf.xif.paper.S2502AwayEquivActual
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.RingTheory.MvPolynomial.Homogeneous

noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2490RestrictionSectionActual
set_option maxHeartbeats 12000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2503OverMapActual

abbrev K : Type := S2490A.K
local instance : Field K := S2490A.fieldK

abbrev G : ℕ → Submodule K (MvPolynomial (Fin 2) K) :=
  MvPolynomial.homogeneousSubmodule (Fin 2) K
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev P1 : Scheme := AlgebraicGeometry.Proj G
abbrev Open : Scheme :=
  Spec (CommRingCat.of (HomogeneousLocalization.Away G (MvPolynomial.X 1)))

abbrev OpenMap : Open ⟶ P1 :=
  AlgebraicGeometry.Proj.awayι G (MvPolynomial.X 1)
    (by rw [MvPolynomial.mem_homogeneousSubmodule]; exact MvPolynomial.isHomogeneous_X K 1)
    (by norm_num)

abbrev SpecMap : Spec (CommRingCat.of (MvPolynomial (Fin 1) K)) ⟶ Open :=
  Spec.map (CommRingCat.ofHom S2502AwayEquivActual.S2502AwayRingEquiv.toRingHom)
abbrev ToP1 : Spec (CommRingCat.of (MvPolynomial (Fin 1) K)) ⟶ P1 :=
  SpecMap ≫ OpenMap

abbrev P1Over : Iut.SchemeOverField K :=
  Over.mk (AlgebraicGeometry.Proj.toSpecZero G ≫
    Spec.map (CommRingCat.ofHom
      ((GradedRing.projZeroRingHom' G).comp
        (MvPolynomial.C : K →+* MvPolynomial (Fin 2) K))))

abbrev FOver : Iut.SchemeOverField K :=
  Over.mk (Spec.map (CommRingCat.ofHom
    (algebraMap K (MvPolynomial (Fin 1) K))))

noncomputable def OverMap : FOver ⟶ P1Over :=
  Over.homMk ToP1 (by
    dsimp [P1Over, FOver, ToP1, SpecMap, OpenMap]
    simp only [Category.assoc]
    rw [AlgebraicGeometry.Proj.awayι_toSpecZero]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    simp [GradedRing.projZeroRingHom'])

#print axioms OverMap
end LeanFormal.IUT.XiFPaper.S2503OverMapActual
end