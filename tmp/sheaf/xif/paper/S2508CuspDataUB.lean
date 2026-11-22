/-
# S2508: the boundary cusp of cK over the unified base UB

This file builds the cusp datum of `S2500CuspData` for the actual orbicurve
`S2495cK` of S2495c, with compactification the projective line over the unified
base `UB = Q(i)` of S2504.

## What is constructed unconditionally

* `S2508FOver`            : the representing scheme `P1_UB = Proj UB[X0,X1]` (S2505);
* `S2508Compactification` : the representable etale stack of `P1_UB`, with the
  stack condition supplied by S2199 (no hypothesis);
* `S2508ResidueScheme`   : the residue scheme `Spec UB` as a `UB`-scheme;
* `S2508ChartMap`        : the affine chart map `Spec UB[x] --> P1_UB`, i.e. the
  actual ring identification `Away UB[X0,X1]_(X1) = UB[x]` of S2505 followed by
  the open immersion `Proj.awayι`; proved to be an open immersion of schemes;
* `S2508ChartOverMap`    : the chart map as a morphism of `UB`-schemes.  The
  structure-map triangle is *proved* from S2505's computation `phi_algebraMap`
  (the chart identification sends base-field constants to constants);
* `S2508StackOpenMap`    : the induced strong transformation of representable
  pseudofunctors (2-Yoneda, S1742), i.e. the stack open map of the chart.

## The exact remaining input

The boundary point at infinity of `P1_UB` is not constructed: Mathlib's `Proj`
point API does not supply the closed point `X1 = 0` in the shape needed here, and
no point is fabricated.  `S2508CuspDatum` therefore carries exactly

* `point : S2508ResidueScheme ⟶ S2508FOver` (the point at infinity),
* `separation : ∀ s, s ≫ S2508ChartOverMap ≠ point` (it is outside the image of
  the affine chart: the scheme-level boundary condition),
* `stackOpenImmersion : EtaleStackOpenImmersion S2508StackOpenMap` (the
  representable-open-immersion property of the chart map of stacks; the
  iso-comma pullback witnesses are not in the tree, cf. S1864 and S1913).

From that datum the `S2500CuspData` is constructed and its `isBoundary` field is
*proved* from `separation` via the 2-Yoneda computation `S1742App_obj`.  Hence
the cusp is unconditional in `S2500CuspData`; only the three scheme-level
inputs above remain.  The axiom audit at the end records the exact cost.
-/
import tmp.sheaf.xif.paper.S2505AwayEquivActual
import tmp.sheaf.xif.paper.S2500CuspDataActual
import tmp.sheaf.xif.paper.S1742TwoYonedaActual
import tmp.sheaf.xif.paper.S2199RepresentableStackActual

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry
open HomogeneousLocalization
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2490RestrictionSectionActual
open LeanFormal.IUT.XiFPaper.S2495cFUnconditionalActual
open LeanFormal.IUT.XiFPaper.S2500CuspDataActual
open LeanFormal.IUT.XiFPaper.S2504UnifiedBaseActual
open LeanFormal.IUT.XiFPaper.S2505AwayEquivActual
open LeanFormal.IUT.XiFPaper.S2199RepresentableStackActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual

namespace LeanFormal.IUT.XiFPaper.S2508CuspDataUB

local instance : Field UB := inferInstance
local instance : CommRing UB := inferInstance
attribute [local instance] MvPolynomial.gradedAlgebra

/-! ## 1. The projective compactification over `UB` -/

/-- The representing scheme of the compactification: the projective line
`P1_UB = Proj UB[X0,X1]` of S2505. -/
noncomputable abbrev S2508FOver : Iut.SchemeOverField UB := S2504P1Over

/-- The affine scheme `Spec UB[x]` over `UB`: the actual model of `cK`. -/
noncomputable abbrev S2508AffineOver : Iut.SchemeOverField UB := S2504FOver'

/-- **The compactification stack**: the representable etale stack of `P1_UB`.
The stack condition is S2199's theorem for representable pseudofunctors. -/
noncomputable def S2508Compactification : Iut.EtaleStackOverField UB where
  fiber := Iut.schemeRepresentableEtalePseudofunctor UB S2508FOver
  isStack := s2199_representable_isStack UB S2508FOver

/-- The fiber of the compactification stack is definitionally the representable
pseudofunctor of `P1_UB`. -/
theorem S2508Compactification_fiber :
    S2508Compactification.fiber =
      Iut.schemeRepresentableEtalePseudofunctor UB S2508FOver := rfl

/-- The compactification stack carries no orbicurve signature. -/
theorem S2508Compactification_signature :
    S2508Compactification.orbicurveSignature = none := rfl

/-- The residue scheme of the boundary point: `Spec UB`, as a `UB`-scheme. -/
noncomputable def S2508ResidueScheme : Iut.SchemeOverField UB :=
  Over.mk (𝟙 (Spec (CommRingCat.of UB)))

/-- The underlying scheme of the residue scheme is `Spec UB`. -/
theorem S2508ResidueScheme_left :
    S2508ResidueScheme.left = Spec (CommRingCat.of UB) := rfl

/-! ## 2. The affine chart `A1 --> P1` -/

/-- The affine chart map `Spec UB[x] ⟶ P1_UB` of the chart `X1 =/= 0`: the ring
identification `Away UB[X0,X1]_(X1) = UB[x]` of S2505 followed by the open
immersion `Proj.awayι`. -/
noncomputable abbrev S2508ChartMap : S2504Dom ⟶ S2504P1 := S2504ToP1

/-- The chart map, written out with the open immersion `Proj.awayι`. -/
theorem S2508ChartMap_unfold :
    S2508ChartMap =
      Spec.map (CommRingCat.ofHom S2504AwayRingEquiv.toRingHom) ≫
        Proj.awayι S2504Grading (MvPolynomial.X 1)
          (by rw [MvPolynomial.mem_homogeneousSubmodule]
              exact MvPolynomial.isHomogeneous_X UB 1)
          (by norm_num) := rfl

/-- The structure morphism of `P1_UB`. -/
theorem S2508FOver_hom :
    S2508FOver.hom = Proj.toSpecZero S2504Grading ≫
      Spec.map (CommRingCat.ofHom
        ((GradedRing.projZeroRingHom' S2504Grading).comp
          (MvPolynomial.C : UB →+* MvPolynomial (Fin 2) UB))) := rfl

/-- The structure morphism of the affine chart `Spec UB[x]`. -/
theorem S2508AffineOver_hom : S2508AffineOver.hom = S2504DomHom := rfl

/-- **The chart map is an open immersion**: the affine line inside `P1` at the
chart `X1 =/= 0`.  The ring identification is an isomorphism and `Proj.awayι`
is an open immersion of schemes. -/
theorem S2508ChartMap_isOpenImmersion : IsOpenImmersion S2508ChartMap := by
  haveI h1 : IsIso (CommRingCat.ofHom S2504AwayRingEquiv.toRingHom) :=
    S2504AwayRingEquiv.toCommRingCatIso.isIso_hom
  haveI h2 : IsIso S2504SpecMap := by
    change IsIso (Spec.map (CommRingCat.ofHom S2504AwayRingEquiv.toRingHom))
    infer_instance
  haveI h3 : IsOpenImmersion S2504OpenMap := by
    change IsOpenImmersion (Proj.awayι S2504Grading (MvPolynomial.X 1) _ _)
    infer_instance
  exact IsOpenImmersion.comp S2504SpecMap S2504OpenMap

/-- **The structure-map triangle of the chart**: the chart map is a morphism of
`UB`-schemes.  This is where the S2505 chart identification is used: it sends
base-field constants to base-field constants (`phi_algebraMap`). -/
theorem S2508ChartMap_structure :
    S2508ChartMap ≫ S2508FOver.hom = S2508AffineOver.hom := by
  have hpt : ∀ c : UB,
      GradedRing.projZeroRingHom' S2504Grading
          (MvPolynomial.C c : MvPolynomial (Fin 2) UB)
        = algebraMap UB (S2504Grading 0) c := by
    intro c
    have hval : (MvPolynomial.C c : MvPolynomial (Fin 2) UB)
        = ↑(algebraMap UB (S2504Grading 0) c) := by
      rw [SetLike.GradeZero.coe_algebraMap, MvPolynomial.algebraMap_eq]
    rw [hval, GradedRing.projZeroRingHom'_apply_coe]
  have hring :
      ((S2504AwayRingEquiv.toRingHom.comp
          (HomogeneousLocalization.fromZeroRingHom S2504Grading
            (Submonoid.powers (MvPolynomial.X 1)))).comp
          ((GradedRing.projZeroRingHom' S2504Grading).comp
            (MvPolynomial.C : UB →+* MvPolynomial (Fin 2) UB)))
        = algebraMap UB (MvPolynomial (Fin 1) UB) := by
    apply RingHom.ext
    intro c
    simp only [RingHom.comp_apply]
    have hg : (HomogeneousLocalization.fromZeroRingHom S2504Grading
        (Submonoid.powers (MvPolynomial.X 1)))
        ((GradedRing.projZeroRingHom' S2504Grading) (MvPolynomial.C c))
        = algebraMap UB (Away S2504Grading (MvPolynomial.X 1)) c := by
      rw [hpt c]
      exact (DFunLike.congr_fun S2502Away_algebraMap c).symm
    rw [hg]
    exact phi_algebraMap c
  rw [S2508ChartMap_unfold, S2508FOver_hom, S2508AffineOver_hom]
  simp only [Category.assoc]
  rw [Proj.awayι_toSpecZero_assoc]
  simp only [← Category.assoc]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [hring]

/-- The chart map as a morphism of `UB`-schemes. -/
noncomputable def S2508ChartOverMap : S2508AffineOver ⟶ S2508FOver :=
  Over.homMk S2508ChartMap S2508ChartMap_structure

/-- The underlying scheme morphism of the chart map is the chart map. -/
theorem S2508ChartOverMap_left :
    S2508ChartOverMap.left = S2508ChartMap := rfl

/-- The scheme chart morphism is an open immersion. -/
theorem S2508ChartOverMap_isOpenImmersion :
    IsOpenImmersion S2508ChartOverMap.left := S2508ChartMap_isOpenImmersion

/-! ## 3. The stack open map of the affine chart (2-Yoneda) -/

/-- The stack open map of the affine chart into the `P1` compactification: the
strong transformation of representable pseudofunctors induced by the scheme
morphism `S2508ChartOverMap` (2-Yoneda comparison of S1742). -/
noncomputable def S2508StackOpenMap : S2495cK.stack.Hom S2508Compactification :=
  S1742StrongTransOfHom S2508ChartOverMap

/-! ## 4. The boundary datum and the cusp -/

/-- The three scheme/stack-level inputs that are not available in the tree: the
point at infinity, its separation from the affine chart, and the representable
open-immersion property of the chart map of stacks. -/
structure S2508CuspDatum where
  /-- The point at infinity of `P1_UB`. -/
  point : S2508ResidueScheme ⟶ S2508FOver
  /-- The point at infinity is outside the image of the affine chart. -/
  separation : ∀ s : S2508ResidueScheme ⟶ S2508AffineOver,
    s ≫ S2508ChartOverMap ≠ point
  /-- The chart map of stacks is representably an open immersion. -/
  stackOpenImmersion : Iut.EtaleStackOpenImmersion S2508StackOpenMap

namespace S2508CuspDatum

variable (D : S2508CuspDatum)

/-- The boundary point of the compactification, as a stack point. -/
noncomputable def boundaryPoint :
    Pseudofunctor.StrongTrans
      (Iut.schemeRepresentableEtalePseudofunctor UB S2508ResidueScheme)
      S2508Compactification.fiber :=
  S1742StrongTransOfHom D.point

/-- The 2-Yoneda computation of the stack open map on a test section. -/
theorem stackOpenMap_app (s : S2508ResidueScheme ⟶ S2508AffineOver) :
    ((S2508StackOpenMap.app
        (LocallyDiscrete.mk (Opposite.op S2508ResidueScheme))).toFunctor.obj
          (Discrete.mk s)) =
      Discrete.mk (s ≫ S2508ChartOverMap) :=
  S1742App_obj S2508ChartOverMap
    (LocallyDiscrete.mk (Opposite.op S2508ResidueScheme)) s

/-- The object selected by the boundary point is the point at infinity. -/
theorem pointObject_eq :
    Iut.OrbicurveFiniteEtaleCover.pointObject S2508ResidueScheme
        (boundaryPoint D) = Discrete.mk D.point := by
  rw [Iut.OrbicurveFiniteEtaleCover.pointObject]
  show (S1742App D.point
      (LocallyDiscrete.mk (Opposite.op S2508ResidueScheme))).toFunctor.obj
        (Discrete.mk (𝟙 S2508ResidueScheme)) = Discrete.mk D.point
  rw [S1742App_obj, Category.id_comp]

/-- **The boundary condition, proved**: no object of `cK` over the residue scheme
maps to the point at infinity, because the whole affine chart misses it. -/
theorem isBoundary :
    ∀ object : S2495cK.stack.fiber.obj
        (LocallyDiscrete.mk (Opposite.op S2508ResidueScheme)),
      IsEmpty
        (((S2508StackOpenMap.app
            (LocallyDiscrete.mk (Opposite.op S2508ResidueScheme))).toFunctor.obj
              object) ≅
          Iut.OrbicurveFiniteEtaleCover.pointObject S2508ResidueScheme
            (boundaryPoint D)) := by
  intro object
  obtain ⟨s⟩ := object
  refine ⟨fun i => D.separation s ?_⟩
  have hi : ((S2508StackOpenMap.app
        (LocallyDiscrete.mk (Opposite.op S2508ResidueScheme))).toFunctor.obj
          (Discrete.mk s)).as =
      (Iut.OrbicurveFiniteEtaleCover.pointObject S2508ResidueScheme
        (boundaryPoint D)).as :=
    Discrete.eq_of_hom i.hom
  rw [stackOpenMap_app s, pointObject_eq D] at hi
  exact hi

/-- **The cusp datum of S2500 for `S2495cK` over the unified base.** -/
noncomputable def cuspData : S2500CuspData where
  compactification := S2508Compactification
  openMap := S2508StackOpenMap
  openImmersion := D.stackOpenImmersion
  residueScheme := S2508ResidueScheme
  point := boundaryPoint D
  isBoundary := isBoundary D

/-- The compactification of the cusp datum is the `P1` stack. -/
theorem cuspData_compactification :
    (cuspData D).compactification = S2508Compactification := rfl

/-- The residue scheme of the cusp datum is `Spec UB`. -/
theorem cuspData_residueScheme :
    (cuspData D).residueScheme = S2508ResidueScheme := rfl

/-- **The boundary cusp of `S2495cK`** obtained from the datum via S2500. -/
noncomputable def boundaryCusp : Iut.OrbicurveBoundaryCusp S2495cK :=
  S2500CuspOfData (cuspData D)

/-- The boundary cusp exists as soon as the boundary datum exists. -/
theorem nonempty_boundaryCusp (h : Nonempty S2508CuspDatum) :
    Nonempty (Iut.OrbicurveBoundaryCusp S2495cK) :=
  h.elim fun D => ⟨boundaryCusp D⟩

end S2508CuspDatum

/-- The exact missing input, as a proposition. -/
def S2508Missing : Prop := Nonempty S2508CuspDatum

/-- The missing proposition is literally the nonemptiness of the datum. -/
theorem S2508Missing_iff : S2508Missing ↔ Nonempty S2508CuspDatum := Iff.rfl

/-! ## 5. Target-locked type checks -/

example : Iut.EtaleStackOverField UB := S2508Compactification
example : Iut.SchemeOverField UB := S2508FOver
example : Iut.SchemeOverField UB := S2508ResidueScheme
example (D : S2508CuspDatum) : S2500CuspData := S2508CuspDatum.cuspData D
example (D : S2508CuspDatum) :
    Iut.OrbicurveBoundaryCusp S2495cK := S2508CuspDatum.boundaryCusp D
example (D : S2508CuspDatum) :
    S2495cK.stack.Hom S2508Compactification := S2508StackOpenMap

/-! ## 6. Axiom audit -/

#print axioms S2508Compactification
#print axioms S2508ChartMap_isOpenImmersion
#print axioms S2508ChartMap_structure
#print axioms S2508ChartOverMap
#print axioms S2508StackOpenMap
#print axioms S2508CuspDatum.pointObject_eq
#print axioms S2508CuspDatum.isBoundary
#print axioms S2508CuspDatum.cuspData
#print axioms S2508CuspDatum.boundaryCusp
#print axioms S2508CuspDatum.nonempty_boundaryCusp

end LeanFormal.IUT.XiFPaper.S2508CuspDataUB
end