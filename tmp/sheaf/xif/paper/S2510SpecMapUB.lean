import tmp.sheaf.xif.paper.S2506P1OverUB
import tmp.sheaf.xif.paper.S2509GenericAwayEquivActual

noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2504UnifiedBaseActual
open LeanFormal.IUT.XiFPaper.S2506P1OverUB
noncomputable local instance : Field UB := inferInstance
noncomputable local instance : CommRing UB := inferInstance
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S2510SpecMapUB

abbrev S2510SpecMap : S2506Dom ⟶ S2506Open :=
  Spec.map (CommRingCat.ofHom (S2509GenericAwayEquiv.fRing UB))

abbrev S2510FOver : Iut.SchemeOverField UB := Over.mk S2506DomHom

abbrev S2510ToP1 : (Over.left S2510FOver) ⟶ (Over.left S2506P1Over) :=
  S2510SpecMap ≫ S2506OpenMap

noncomputable def S2510OverMap : S2510FOver ⟶ S2506P1Over :=
  let e1 : (Over.left S2510FOver) = S2506Dom := rfl
  let e2 : S2506P1 = (Over.left S2506P1Over) := rfl
  Over.homMk ((eqToHom e1) ≫ S2506ToP1 ≫ (eqToHom e2)) (by
    dsimp [S2506P1Over, S2510FOver, S2510ToP1, S2510SpecMap, S2506OpenMap]
    rw [← Category.assoc]
    rw [AlgebraicGeometry.Proj.awayι_toSpecZero]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    simp [GradedRing.projZeroRingHom', S2509GenericAwayEquiv.fRing])

#print axioms S2510OverMap
end LeanFormal.IUT.XiFPaper.S2510SpecMapUB
end