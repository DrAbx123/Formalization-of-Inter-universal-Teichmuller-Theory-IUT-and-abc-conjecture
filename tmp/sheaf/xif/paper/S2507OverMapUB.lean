/-
# S2507: the structure morphism `S2504FOver' ⟶ S2504P1Over` over the unified base `UB`

This file constructs the morphism of schemes over `Spec UB`

    S2507OverMap : S2504FOver' ⟶ S2504P1Over

between the affine line `S2504FOver' = Over.mk S2504DomHom` and the projective
line `S2504P1Over` of `S2505AwayEquivActual`, both over the unified base
`UB = S2480QiActual.F`.

The underlying morphism of schemes is the chart morphism `S2504ToP1` (the
composition of `Spec` of the chart identification `Away 𝒜 (X 1) ≃+* UB[X]`
with the open immersion `awayι` of the chart `X 1 ≠ 0`).  The compatibility
triangle with the two structure morphisms is the identity
`awayι ≫ toSpecZero = Spec.map (fromZeroRingHom ...)` of Mathlib
(`AlgebraicGeometry.Proj.awayι_toSpecZero`), through which both sides reduce
to the ring map `UB → UB[X]` of constants.

No `sorry`, no new axiom.
-/
import tmp.sheaf.xif.paper.S2504UnifiedBaseActual
import tmp.sheaf.xif.paper.S2505AwayEquivActual

noncomputable section

open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2504UnifiedBaseActual
open LeanFormal.IUT.XiFPaper.S2505AwayEquivActual

set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S2507OverMapUB

local instance : Field UB := inferInstance
local instance : CommRing UB := inferInstance
attribute [local instance] MvPolynomial.gradedAlgebra

/-! ## 1. The degree-zero projection fixes the constants -/

/-- The projection onto the degree-zero component fixes the constants. -/
theorem S2507_coe_projZeroRingHom (c : UB) :
    (GradedRing.projZeroRingHom S2504Grading (MvPolynomial.C c) : MvPolynomial (Fin 2) UB)
      = MvPolynomial.C c := by
  have hmem : (MvPolynomial.C c : MvPolynomial (Fin 2) UB) ∈ S2504Grading 0 := by
    rw [MvPolynomial.mem_homogeneousSubmodule]
    exact MvPolynomial.isHomogeneous_C (σ := Fin 2) (R := UB) c
  rw [GradedRing.projZeroRingHom_apply]
  exact DirectSum.decompose_of_mem_same S2504Grading hmem

/-- The ring homomorphism `projZeroRingHom'` fixes the constants, viewed as
elements of the degree-zero submodule. -/
theorem S2507_projZeroRingHom'_C (c : UB) :
    GradedRing.projZeroRingHom' S2504Grading (MvPolynomial.C c)
      = algebraMap UB (S2504Grading 0) c := by
  apply Subtype.ext
  rw [GradedRing.coe_projZeroRingHom'_apply, S2507_coe_projZeroRingHom c]
  simp

/-- `fromZeroRingHom` of the degree-zero projection of a constant is the image
of that constant under the structure map of the chart ring. -/
theorem S2507_fromZeroRingHom_C (c : UB) :
    HomogeneousLocalization.fromZeroRingHom S2504Grading (Submonoid.powers (MvPolynomial.X 1))
        (GradedRing.projZeroRingHom' S2504Grading (MvPolynomial.C c))
      = algebraMap UB (HomogeneousLocalization.Away S2504Grading (MvPolynomial.X 1)) c := by
  rw [S2507_projZeroRingHom'_C c, S2502Away_algebraMap, RingHom.comp_apply]

/-! ## 2. The morphism over `Spec UB` -/

/-- **S2507**: the morphism from the affine line to the projective line over
`Spec UB`, obtained from the chart `X 1 ≠ 0`. -/
noncomputable def S2507OverMap : S2504FOver' ⟶ S2504P1Over :=
  Over.homMk S2504ToP1 (by
    change (S2504SpecMap ≫ S2504OpenMap) ≫
        (AlgebraicGeometry.Proj.toSpecZero S2504Grading ≫
          Spec.map (CommRingCat.ofHom
            ((GradedRing.projZeroRingHom' S2504Grading).comp
              (MvPolynomial.C : UB →+* MvPolynomial (Fin 2) UB))))
      = Spec.map (CommRingCat.ofHom (algebraMap UB (MvPolynomial (Fin 1) UB)))
    rw [show (S2504SpecMap ≫ S2504OpenMap) ≫
          (AlgebraicGeometry.Proj.toSpecZero S2504Grading ≫
            Spec.map (CommRingCat.ofHom
              ((GradedRing.projZeroRingHom' S2504Grading).comp
                (MvPolynomial.C : UB →+* MvPolynomial (Fin 2) UB))))
        = S2504SpecMap ≫ (S2504OpenMap ≫ AlgebraicGeometry.Proj.toSpecZero S2504Grading) ≫
            Spec.map (CommRingCat.ofHom
              ((GradedRing.projZeroRingHom' S2504Grading).comp
                (MvPolynomial.C : UB →+* MvPolynomial (Fin 2) UB))) from by
      simp only [Category.assoc]]
    rw [AlgebraicGeometry.Proj.awayι_toSpecZero]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    change S2504AwayRingEquiv.toRingHom
        (HomogeneousLocalization.fromZeroRingHom S2504Grading (Submonoid.powers (MvPolynomial.X 1))
          (GradedRing.projZeroRingHom' S2504Grading (MvPolynomial.C x)))
      = algebraMap UB (MvPolynomial (Fin 1) UB) x
    rw [S2507_fromZeroRingHom_C x]
    exact phi_algebraMap x)

#print axioms S2507OverMap

end LeanFormal.IUT.XiFPaper.S2507OverMapUB
end
