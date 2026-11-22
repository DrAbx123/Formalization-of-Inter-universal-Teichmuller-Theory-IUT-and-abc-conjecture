/-
# S2511: the point at infinity `[1 : 0]` of `P¹_UB`, as a morphism over `UB`

`S2508CuspDataUB` carries three scheme/stack-level inputs for the boundary cusp of
`S2495cK`; the first is the point at infinity

    point : S2508ResidueScheme ⟶ S2508FOver

of the projective line `P¹_UB = Proj UB[X₀,X₁]`.  This file constructs it, as an
object of the slice category `Over (Spec UB)`, with the structure triangle proved
(no hypothetical datum is introduced).

## Construction

The closed point `[1 : 0]` lies in the affine chart `X 0 ≠ 0`, whose ring is the
degree-zero part `Away 𝒜 (X 0)` of the homogeneous localization of `UB[X₀,X₁]`
at `X 0`.  The residue field at `[1 : 0]` is `UB` itself, with structure ring map
the evaluation

    phi0 : UB[X₀,X₁] →+* UB,   X 0 ↦ 1,  X 1 ↦ 0,

extended to the chart ring along the unit `phi0 (X 0) = 1` by
`Localization.awayLift`; this is `chart0 : Away 𝒜 (X 0) →+* UB`.  Applying `Spec`
and then the chart open immersion `Proj.awayι` gives the scheme morphism

    S2511pointMap : Spec UB ⟶ P¹_UB.

The compatibility triangle over `Spec UB` follows from Mathlib's identity
`Proj.awayι_toSpecZero : awayι ≫ toSpecZero = Spec.map (fromZeroRingHom)`
together with the ring identity

    chart0 ∘ fromZeroRingHom ∘ projZeroRingHom' ∘ C = id

on `UB` (`S2511_ring_comp`), whose proof is: `projZeroRingHom'` fixes constants,
`fromZeroRingHom` sends them to the constants of the chart ring, and `chart0`
evaluates a constant at the residue field `UB` of `[1 : 0]`.

Hence `S2511Point : S2508ResidueScheme ⟶ S2508FOver` is an honest morphism of
`UB`-schemes, unconditionally.

No `sorry`, no `axiom`, no new hypothesis.  The axiom audit at the end records the
exact cost.
-/
import tmp.sheaf.xif.paper.S2508CuspDataUB

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2504UnifiedBaseActual
open LeanFormal.IUT.XiFPaper.S2505AwayEquivActual
open LeanFormal.IUT.XiFPaper.S2508CuspDataUB

namespace LeanFormal.IUT.XiFPaper.S2511InfinityPointUB

local instance : Field UB := inferInstance
local instance : CommRing UB := inferInstance
attribute [local instance] MvPolynomial.gradedAlgebra

/-! ## 1. The residue-field evaluation at `[1 : 0]` -/

/-- The projective coordinate `X 0` of `UB[X₀,X₁]`, whose non-vanishing is the
affine chart containing the point `[1 : 0]`. -/
abbrev S2511X0 : MvPolynomial (Fin 2) UB := MvPolynomial.X 0

/-- **Evaluation at `[1 : 0]`**: the ring map `X 0 ↦ 1`, `X 1 ↦ 0`. -/
noncomputable def S2511phi0 : MvPolynomial (Fin 2) UB →+* UB :=
  MvPolynomial.eval₂Hom (RingHom.id UB) (fun i : Fin 2 => if i = 0 then (1 : UB) else 0)

/-- The evaluation at `[1 : 0]` sends the chart coordinate `X 0` to `1`. -/
theorem S2511phi0_X0 : S2511phi0 S2511X0 = 1 := by
  simp [S2511phi0, S2511X0]

/-- `X 0` becomes a unit of `UB` at the point `[1 : 0]`. -/
theorem S2511phi0_isUnit : IsUnit (S2511phi0 S2511X0) := by
  rw [S2511phi0_X0]
  exact isUnit_one

/-- `X 0` is homogeneous of degree one, so that `Proj.awayι` applies to the
chart `X 0 ≠ 0`. -/
theorem S2511X0_mem : S2511X0 ∈ S2504Grading 1 := by
  rw [MvPolynomial.mem_homogeneousSubmodule]
  exact MvPolynomial.isHomogeneous_X UB 0

/-! ## 2. The chart ring map and the scheme morphism -/

/-- **The chart ring map of the point `[1 : 0]`**: the evaluation above,
extended to the homogeneous localization `Away 𝒜 (X 0)` where `X 0` becomes a
unit. -/
noncomputable def S2511chart0 : Away S2504Grading S2511X0 →+* UB :=
  (Localization.awayLift S2511phi0 S2511X0 S2511phi0_isUnit).comp
    (algebraMap (Away S2504Grading S2511X0) (Localization.Away S2511X0))

/-- `Spec` of the chart ring map: the residue-field point of the chart
`X 0 ≠ 0`. -/
noncomputable def S2511pointChart :
    Spec (CommRingCat.of UB) ⟶ Spec (CommRingCat.of (Away S2504Grading S2511X0)) :=
  Spec.map (CommRingCat.ofHom S2511chart0)

/-- **The point at infinity as a morphism of schemes**: the residue-field point
`[1 : 0]` of the chart `X 0 ≠ 0`, followed by the open immersion of the chart
into `P¹_UB`. -/
noncomputable def S2511pointMap : Spec (CommRingCat.of UB) ⟶ S2504P1 :=
  S2511pointChart ≫ Proj.awayι S2504Grading S2511X0 S2511X0_mem (by norm_num)

/-! ## 3. The structure triangle over `Spec UB` -/

/-- The localization map to `Localization.Away (X 0)` is the class of a
degree-zero homogeneous fraction `y / 1`. -/
theorem S2511_algebraMap_away (y : S2504Grading 0) :
    algebraMap (Away S2504Grading S2511X0) (Localization.Away S2511X0)
        (HomogeneousLocalization.fromZeroRingHom S2504Grading
          (Submonoid.powers S2511X0) y)
      = Localization.mk ((y : MvPolynomial (Fin 2) UB)) 1 := rfl

/-- The degree-zero projection fixes the constants, viewed in `𝒜 0`. -/
theorem S2511_projZeroRingHom'_C (c : UB) :
    GradedRing.projZeroRingHom' S2504Grading (MvPolynomial.C c)
      = algebraMap UB (S2504Grading 0) c := by
  have hval : (MvPolynomial.C c : MvPolynomial (Fin 2) UB)
      = ↑(algebraMap UB (S2504Grading 0) c) := by
    rw [SetLike.GradeZero.coe_algebraMap, MvPolynomial.algebraMap_eq]
  rw [hval, GradedRing.projZeroRingHom'_apply_coe]

/-- The degree-zero projection of a constant is that constant. -/
theorem S2511_coe_projZeroRingHom'_C (c : UB) :
    ((GradedRing.projZeroRingHom' S2504Grading (MvPolynomial.C c) : S2504Grading 0)
      : MvPolynomial (Fin 2) UB) = MvPolynomial.C c := by
  rw [S2511_projZeroRingHom'_C, SetLike.GradeZero.coe_algebraMap,
    MvPolynomial.algebraMap_eq]

/-- **The ring identity of the structure triangle**: after the degree-zero
projection and the localization of constants, the chart ring map of `[1 : 0]`
is the identity of `UB`. -/
theorem S2511_ring_comp :
    S2511chart0.comp
        ((HomogeneousLocalization.fromZeroRingHom S2504Grading
            (Submonoid.powers S2511X0)).comp
          ((GradedRing.projZeroRingHom' S2504Grading).comp
            (MvPolynomial.C : UB →+* MvPolynomial (Fin 2) UB)))
      = RingHom.id UB := by
  apply RingHom.ext
  intro c
  simp only [RingHom.comp_apply, RingHom.id_apply, S2511chart0]
  rw [S2511_algebraMap_away, S2511_coe_projZeroRingHom'_C]
  have hv : S2511phi0 S2511X0 * (1 : UB) = 1 := by
    rw [S2511phi0_X0, one_mul]
  rw [show (1 : Submonoid.powers S2511X0) = ⟨S2511X0 ^ 0, ⟨0, rfl⟩⟩ from rfl]
  rw [Localization.awayLift_mk S2511phi0 S2511X0 (MvPolynomial.C c) 1 hv 0]
  simp [S2511phi0, MvPolynomial.eval₂Hom_C]

/-- **The structure triangle of the point at infinity**: the point `[1 : 0]`
is a morphism of `UB`-schemes. -/
theorem S2511pointMap_structure :
    S2511pointMap ≫ S2508FOver.hom = S2508ResidueScheme.hom := by
  have hres : S2508ResidueScheme.hom = 𝟙 (Spec (CommRingCat.of UB)) := rfl
  rw [S2508FOver_hom, hres]
  rw [show S2511pointMap ≫
        (Proj.toSpecZero S2504Grading ≫ Spec.map (CommRingCat.ofHom
          ((GradedRing.projZeroRingHom' S2504Grading).comp
            (MvPolynomial.C : UB →+* MvPolynomial (Fin 2) UB))))
      = S2511pointChart ≫
          (Proj.awayι S2504Grading S2511X0 S2511X0_mem (by norm_num) ≫
            Proj.toSpecZero S2504Grading) ≫
          Spec.map (CommRingCat.ofHom
            ((GradedRing.projZeroRingHom' S2504Grading).comp
              (MvPolynomial.C : UB →+* MvPolynomial (Fin 2) UB))) from by
    simp only [S2511pointMap, Category.assoc]]
  rw [Proj.awayι_toSpecZero]
  rw [← Spec.map_comp]
  rw [show S2511pointChart = Spec.map (CommRingCat.ofHom S2511chart0) from rfl]
  rw [← Spec.map_comp]
  rw [← Spec.map_id (CommRingCat.of UB)]
  refine congrArg Spec.map ?_
  rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_id]
  exact congrArg CommRingCat.ofHom S2511_ring_comp

/-! ## 4. The point at infinity as an object of the slice category -/

/-- **The point at infinity `[1 : 0]` of `P¹_UB`, as a morphism over `Spec UB`.**
This is the first scheme-level input `point` of `S2508CuspDatum`. -/
noncomputable def S2511Point : S2508ResidueScheme ⟶ S2508FOver :=
  Over.homMk S2511pointMap S2511pointMap_structure

/-- The underlying scheme morphism of the point at infinity is
`S2511pointMap`. -/
theorem S2511Point_left :
    S2511Point.left = S2511pointMap := rfl

/-- The structure triangle of the point at infinity, in the form of `Over.w`. -/
theorem S2511Point_w :
    S2511Point.left ≫ S2508FOver.hom = S2508ResidueScheme.hom :=
  Over.w S2511Point

/-! ## 5. Target-locked type checks -/

/-- Type lock: the point at infinity has exactly the frozen target type. -/
example : S2508ResidueScheme ⟶ S2508FOver := S2511Point
example : (Over.mk (𝟙 (Spec (CommRingCat.of UB)))) ⟶ S2504P1Over := S2511Point
example : S2508ResidueScheme.left ⟶ S2508FOver.left := S2511Point.left
example : S2511Point.left = S2511pointMap := S2511Point_left
example : S2508ResidueScheme = Over.mk (𝟙 (Spec (CommRingCat.of UB))) := rfl
example : S2508FOver = S2504P1Over := rfl
example : S2511Point.left ≫ S2508FOver.hom = S2508ResidueScheme.hom := S2511Point_w
example : S2511pointMap ≫ S2508FOver.hom = S2508ResidueScheme.hom :=
  S2511pointMap_structure

/-- Type lock: the point is a morphism in `Over (Spec UB)`, i.e. in
`Iut.SchemeOverField UB`. -/
example : Iut.SchemeOverField UB := S2508ResidueScheme
example : Iut.SchemeOverField UB := S2508FOver

/-! ## 6. The first field of the cusp datum is now available -/

/-- The point at infinity supplies the `point` field of `S2508CuspDatum`; the
other two fields are untouched by this file. -/
theorem S2511Point_exists : ∃ p : S2508ResidueScheme ⟶ S2508FOver, True :=
  ⟨S2511Point, trivial⟩

/-! ## 7. Axiom audit -/

#print axioms S2511phi0
#print axioms S2511chart0
#print axioms S2511pointChart
#print axioms S2511pointMap
#print axioms S2511_ring_comp
#print axioms S2511pointMap_structure
#print axioms S2511Point
#print axioms S2511Point_w

end LeanFormal.IUT.XiFPaper.S2511InfinityPointUB
end
