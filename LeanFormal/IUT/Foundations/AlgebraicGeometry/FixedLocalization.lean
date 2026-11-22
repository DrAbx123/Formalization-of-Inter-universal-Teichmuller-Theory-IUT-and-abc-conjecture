import LeanFormal.IUT.Foundations.AlgebraicGeometry.FixedLocalizationAction

/-! # Goal 3 fixed-localization: fixed-point functor for G-equivariant equivalences

This scratch constructs the fixed-point subring functoriality used by the
affine-intersection square.  The full two-step commuting square is not yet
completed here; see the residual note in the report.  No production edits. -/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace LeanFormal.N8.FixedLocalizationAction

open LeanFormal.N8.FixedLocalizationAction

variable {G : Type*} [Group G]

/-- The inverse of a G-equivariant ring equivalence is again G-equivariant. -/
theorem ringEquiv_symm_smul
    {X Y : Type*} [CommRing X] [CommRing Y]
    [MulSemiringAction G X] [MulSemiringAction G Y]
    (e : X ≃+* Y) (he : ∀ (g : G) (x : X), e (g • x) = g • e x)
    (g : G) (y : Y) : e.symm (g • y) = g • e.symm y := by
  apply e.injective
  rw [e.apply_symm_apply, he g (e.symm y), e.apply_symm_apply]

/-- A G-equivariant ring equivalence induces a ring equivalence of fixed-point
subrings. -/
noncomputable def fixedPointsRingEquiv
    {X Y : Type*} [CommRing X] [CommRing Y]
    [MulSemiringAction G X] [MulSemiringAction G Y]
    (e : X ≃+* Y) (he : ∀ (g : G) (x : X), e (g • x) = g • e x) :
    FixedPoints.subring X G ≃+* FixedPoints.subring Y G where
  toFun x := ⟨e x, by
    change ∀ g : G, g • e (x : X) = e (x : X)
    intro g
    rw [← he]
    exact congrArg e (x.2 g)⟩
  invFun y := ⟨e.symm y, by
    change ∀ g : G, g • e.symm (y : Y) = e.symm (y : Y)
    intro g
    rw [← ringEquiv_symm_smul e he g (y : Y)]
    exact congrArg e.symm (y.2 g)⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv y := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    simp
  map_add' x y := by
    apply Subtype.ext
    simp

@[simp]
theorem fixedPointsRingEquiv_apply_coe
    {X Y : Type*} [CommRing X] [CommRing Y]
    [MulSemiringAction G X] [MulSemiringAction G Y]
    (e : X ≃+* Y) (he : ∀ (g : G) (x : X), e (g • x) = g • e x)
    (x : FixedPoints.subring X G) :
    ((fixedPointsRingEquiv e he x : FixedPoints.subring Y G) : Y) = e (x : X) :=
  rfl

end LeanFormal.N8.FixedLocalizationAction
