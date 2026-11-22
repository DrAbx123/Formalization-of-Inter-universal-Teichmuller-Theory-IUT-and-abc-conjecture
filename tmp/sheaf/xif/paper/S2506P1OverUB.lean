/-
# S2506: the projective line over the unified base `UB`, with its structure morphism

This file assembles the projective line `P¹_UB` **together with its structural
morphism to `Spec UB`**, in a single self-contained namespace on the unified
base `UB = S2480QiActual.F` of `S2504UnifiedBaseActual`.

The chart identification `Away 𝒜 (X 1) ≃+* UB[X]` is the one proved in
`S2505AwayEquivActual` (`S2504AwayRingEquiv`); the base is the unified `UB`.
All objects below live over the local `Field`/`CommRing` instances of `UB`
and the local `MvPolynomial.gradedAlgebra` instance for the homogeneous
grading of `UB[X₀, X₁]`.

No `sorry`, no new axiom.

## Main definitions

* `S2506Grading` — the degree grading of `UB[X₀, X₁]`.
* `S2506P1` — `Proj` of the grading, the projective line over `UB`.
* `S2506Open` — `Spec` of the degree-zero part of the localization at `X 1`.
* `S2506OpenMap` — the open immersion of the chart into the projective line.
* `S2506Dom` — the affine line `Spec UB[X]`.
* `S2506DomHom` — the structure morphism of the affine line.
* `S2506SpecMap` — `Spec` of the chart identification.
* `S2506ToP1` — the chart morphism `Spec UB[X] ⟶ P¹_UB`.
* `S2506P1Over` — the projective line as an object over `Spec UB`.
-/

import tmp.sheaf.xif.paper.S2504UnifiedBaseActual
import tmp.sheaf.xif.paper.S2505AwayEquivActual
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.RingTheory.MvPolynomial.Homogeneous

noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2504UnifiedBaseActual
open LeanFormal.IUT.XiFPaper.S2505AwayEquivActual
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S2506P1OverUB

local instance : Field UB := inferInstance
local instance : CommRing UB := inferInstance

/-- The degree grading of the polynomial ring in the two projective
coordinates `X 0`, `X 1` over the unified base `UB`. -/
abbrev S2506Grading : ℕ → Submodule UB (MvPolynomial (Fin 2) UB) :=
  MvPolynomial.homogeneousSubmodule (Fin 2) UB
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The projective line over `UB`. -/
abbrev S2506P1 : Scheme := AlgebraicGeometry.Proj S2506Grading

/-- The affine chart `X 1 ≠ 0` of the projective line. -/
abbrev S2506Open : Scheme :=
  Spec (CommRingCat.of (HomogeneousLocalization.Away S2506Grading (MvPolynomial.X 1)))

/-- The open immersion of the chart `X 1 ≠ 0` into the projective line. -/
abbrev S2506OpenMap : S2506Open ⟶ S2506P1 :=
  AlgebraicGeometry.Proj.awayι S2506Grading (MvPolynomial.X 1)
    (by rw [MvPolynomial.mem_homogeneousSubmodule]; exact MvPolynomial.isHomogeneous_X UB 1)
    (by norm_num)

/-- The affine line `Spec UB[X]`. -/
abbrev S2506Dom : Scheme := Spec (CommRingCat.of (MvPolynomial (Fin 1) UB))

/-- The structure morphism of the affine line over `UB`. -/
abbrev S2506DomHom : S2506Dom ⟶ Spec (CommRingCat.of UB) :=
  Spec.map (CommRingCat.ofHom (algebraMap UB (MvPolynomial (Fin 1) UB)))

/-- The chart identification at the level of schemes. -/
abbrev S2506SpecMap : S2506Dom ⟶ S2506Open :=
  Spec.map (CommRingCat.ofHom S2504AwayRingEquiv.toRingHom)

/-- The morphism from the affine line to the projective line through the chart. -/
abbrev S2506ToP1 : S2506Dom ⟶ S2506P1 :=
  S2506SpecMap ≫ S2506OpenMap

/-- The projective line as an object over `Spec UB`. -/
abbrev S2506P1Over : Iut.SchemeOverField UB :=
  Over.mk (AlgebraicGeometry.Proj.toSpecZero S2506Grading ≫
    Spec.map (CommRingCat.ofHom
      ((GradedRing.projZeroRingHom' S2506Grading).comp
        (MvPolynomial.C : UB →+* MvPolynomial (Fin 2) UB))))

/-! ## 1. Type locks for the frozen interface -/

example : (S2506Grading : ℕ → Submodule UB (MvPolynomial (Fin 2) UB)) =
    MvPolynomial.homogeneousSubmodule (Fin 2) UB := rfl
example : S2506P1 = AlgebraicGeometry.Proj S2506Grading := rfl
example : S2506Open = Spec (CommRingCat.of
    (HomogeneousLocalization.Away S2506Grading (MvPolynomial.X 1))) := rfl
example : S2506Dom = Spec (CommRingCat.of (MvPolynomial (Fin 1) UB)) := rfl
example : S2506DomHom = Spec.map (CommRingCat.ofHom
    (algebraMap UB (MvPolynomial (Fin 1) UB))) := rfl
example : S2506SpecMap = Spec.map (CommRingCat.ofHom
    S2504AwayRingEquiv.toRingHom) := rfl
example : S2506ToP1 = S2506SpecMap ≫ S2506OpenMap := rfl
example : S2506P1Over.left = S2506P1 := rfl

/-! ## 2. Axiom audit -/

#print axioms S2506Grading
#print axioms S2506P1
#print axioms S2506Open
#print axioms S2506OpenMap
#print axioms S2506Dom
#print axioms S2506DomHom
#print axioms S2506SpecMap
#print axioms S2506ToP1
#print axioms S2506P1Over

end LeanFormal.IUT.XiFPaper.S2506P1OverUB
end
