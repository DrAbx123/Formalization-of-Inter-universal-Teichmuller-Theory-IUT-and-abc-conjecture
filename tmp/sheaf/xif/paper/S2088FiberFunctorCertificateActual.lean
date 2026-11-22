/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal IUT/ABC contributors
-/
import tmp.sheaf.xif.paper.S2070CurveEtaleFundamentalCardActual
import tmp.sheaf.xif.paper.S2074CurveFiberFintypeActual
import tmp.sheaf.xif.paper.S2081CurveCardM2Actual
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic

/-!
# S2088 -- the six `FiberFunctorCertificate` obligations for
`curveGeometricFiberFunctorFintype`

The target is the `Prop`-structure `FiberFunctorCertificate` frozen in S2070
(`tmp/sheaf/xif/paper/S2070CurveEtaleFundamentalCardActual.lean`), whose six
fields are the (G4)-(G6) obligations of a fiber functor for the geometric fiber
functor of the once-punctured curve y^2 = x^3 - x:

1. `preservesTerminalObjects`
2. `preservesPullbacks`
3. `preservesFiniteCoproducts`
4. `preservesEpis`
5. `preservesQuotientsByFiniteGroups`
6. `reflectsIsos`

The functor is `curveGeometricFiberFunctorFintype K hfin`, the `FintypeCat`-valued
lift (S2070/S2074) of the Type-valued geometric fiber functor
`curveGeometricFiberFunctor K Omega x`, whose value at a finite etale cover `Y` is
the type of lifts of the geometric point `x : Spec Omega -> X` to `Y`; the
finiteness input `hfin` is discharged unconditionally in S2074/S2081.

## What this file proves

* **Transfer layer.** Since `curveGeometricFiberFunctorFintype K hfin` is
  `ObjectProperty.lift (fun T => Finite T) _ hfin` and `FintypeCat.incl` is fully
  faithful, each of the six obligations for the `FintypeCat`-valued functor is
  equivalent to the corresponding obligation for the *Type-valued* geometric
  fiber functor.  This is proved generically for limits and colimits
  (`preservesLimitsOfShape_of_comp_of_reflects`,
  `preservesColimitsOfShape_of_comp_of_reflects`) and taken from Mathlib for
  epimorphisms and isomorphisms.

* **Item 1 (terminal objects): proved unconditionally.**
  `certificate_preservesTerminalObjects`.

* **Items 2-6: isolated as the five fields of `RemainingTypeLevel`.**  Each is
  stated verbatim as the corresponding certificate field for the Type-valued
  geometric fiber functor, and the implication "remaining type-level statement
  => certificate field" is proved (`certificate_preservesPullbacks`,
  `certificate_preservesFiniteCoproducts`, `certificate_preservesEpis`,
  `certificate_preservesQuotientsByFiniteGroups`, `certificate_reflectsIsos`,
  `certificate_of_remaining`).  No inhabitant is asserted.

## Honest boundary

No `axiom`, no `sorry`, no `Nonempty` wrapper for the isolated items.  Item 1
is proved unconditionally for the actual functor; the other five are
*hypotheses* of the theorems that consume them.  See section 8 for the precise
mathematical content of each isolated item (item 2 is a formalization gap of
this file only: its statement is true and no Mathlib object is missing for it;
items 3-6 need mathematical input not available in Mathlib 4.32.2).
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1600000

namespace LeanFormal.IUT.XiFPaper.S2088FiberFunctorCertificateActual

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open LeanFormal.IUT.Foundations.Geometry
open LeanFormal.IUT.XiFPaper.S2070CurveEtaleFundamentalCardActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36

universe u

/-! ## 1. Transfer along a fully faithful inclusion

If `F ⋙ G` preserves a class of limits and `G` reflects them, then `F`
preserves them.  Applied to `G = FintypeCat.incl` this reduces the
`FintypeCat`-valued obligations to the `Type`-valued ones. -/

section Transfer

variable {C : Type*} [Category C] {D : Type*} [Category D] {E : Type*} [Category E]
variable {J : Type*} [Category J]

/-- Preservation of limits of shape `J` transfers from a composite along a
reflecting functor. -/
theorem preservesLimitsOfShape_of_comp_of_reflects (F : C ⥤ D) (G : D ⥤ E)
    [ReflectsLimitsOfShape J G] [PreservesLimitsOfShape J (F ⋙ G)] :
    PreservesLimitsOfShape J F where
  preservesLimit := fun {K} =>
    ⟨fun {c} hc => by
      have h1 : IsLimit ((F ⋙ G).mapCone c) := isLimitOfPreserves (F ⋙ G) hc
      have h2 : IsLimit (G.mapCone (F.mapCone c)) := h1
      exact ⟨isLimitOfReflects G h2⟩⟩

/-- Preservation of colimits of shape `J` transfers from a composite along a
reflecting functor. -/
theorem preservesColimitsOfShape_of_comp_of_reflects (F : C ⥤ D) (G : D ⥤ E)
    [ReflectsColimitsOfShape J G] [PreservesColimitsOfShape J (F ⋙ G)] :
    PreservesColimitsOfShape J F where
  preservesColimit := fun {K} =>
    ⟨fun {c} hc => by
      have h1 : IsColimit ((F ⋙ G).mapCocone c) := isColimitOfPreserves (F ⋙ G) hc
      have h2 : IsColimit (G.mapCocone (F.mapCocone c)) := h1
      exact ⟨isColimitOfReflects G h2⟩⟩

end Transfer

/-! ## 2. The Type-valued geometric fiber functor: evaluation lemmas -/

section Fiber

variable {S : Scheme.{u}} {Omega : Type u} [Field Omega]
  {x : Spec (CommRingCat.of Omega) ⟶ S}

/-- The Type-valued geometric fiber functor acts on morphisms by postcomposition
of lifts. -/
theorem geometricFiberFunctor_map_apply {Y Z : FiniteEtaleCover S} (f : Y ⟶ Z)
    (s : geometricFiberObject Omega x Y) :
    (geometricFiberFunctor Omega x).map f s = geometricFiberMap f s := rfl

/-- The underlying scheme morphism of the geometric fiber after a morphism of
covers. -/
theorem geometricFiberMap_val {Y Z : FiniteEtaleCover S} (f : Y ⟶ Z)
    (s : geometricFiberObject Omega x Y) :
    (geometricFiberMap f s).1 = s.1 ≫ Over.Hom.left f.1 := rfl

/-! ## 3. Item 1: preservation of terminal objects -/

/-- The geometric fiber over any terminal finite etale cover is a terminal object
of `Type`: a terminal cover is isomorphic to the identity cover, whose fiber is
the singleton of the geometric point itself. -/
noncomputable def isTerminal_obj_of_isTerminal {T : FiniteEtaleCover S} (hT : IsTerminal T) :
    IsTerminal ((geometricFiberFunctor Omega x).obj T) := by
  have h0 : IsTerminal (terminalCover S) := finiteEtaleCover_terminalCover_isTerminal S
  have e : T ≅ terminalCover S := hT.uniqueUpToIso h0
  have h1 : IsTerminal ((geometricFiberFunctor Omega x).obj (terminalCover S)) := by
    have hy : Unique ((geometricFiberFunctor Omega x).obj (terminalCover S)) := by
      change Unique {s : Spec (CommRingCat.of Omega) ⟶ S // s ≫ 𝟙 S = x}
      refine ⟨⟨⟨x, Category.comp_id x⟩⟩, ?_⟩
      intro a
      apply Subtype.ext
      simpa using a.2
    haveI hU : ∀ Y : Type u,
        Unique (Y ⟶ (geometricFiberFunctor Omega x).obj (terminalCover S)) := by
      intro Y
      refine ⟨⟨TypeCat.ofHom (fun _ => default)⟩, ?_⟩
      intro a
      apply ConcreteCategory.hom_ext
      intro y
      exact Subsingleton.elim _ _
    exact IsTerminal.ofUnique _
  exact IsTerminal.ofIso h1 ((geometricFiberFunctor Omega x).mapIso e).symm

/-- The geometric fiber functor preserves the limit of the empty diagram. -/
theorem preservesLimit_empty :
    PreservesLimit (Functor.empty.{0} (FiniteEtaleCover S))
      (geometricFiberFunctor Omega x) := by
  refine preservesLimit_of_preserves_limit_cone (t := asEmptyCone (terminalCover S))
    (finiteEtaleCover_terminalCover_isTerminal S) ?_
  exact (isLimitMapConeEmptyConeEquiv (geometricFiberFunctor Omega x) (terminalCover S)).symm
    (isTerminal_obj_of_isTerminal (finiteEtaleCover_terminalCover_isTerminal S))

/-- **Item 1 at the Type level.**  The geometric fiber functor preserves
terminal objects. -/
theorem preservesTerminalObjects_typeLevel :
    PreservesLimitsOfShape (Discrete PEmpty.{1}) (geometricFiberFunctor (X := S) Omega x) := by
  haveI : PreservesLimit (Functor.empty.{0} (FiniteEtaleCover S))
      (geometricFiberFunctor Omega x) := preservesLimit_empty (Omega := Omega) (x := x)
  exact preservesLimitsOfShape_pempty_of_preservesTerminal _

end Fiber

/-! ## 4. Item 1 at the curve level, and the transfer layer -/

section Curve

variable {K : Type u} [Field K] {Omega : Type u} [Field Omega]
  {x : Spec (CommRingCat.of Omega) ⟶ CurveBase K}

/-- Item 1 for the actual curve fiber functor, Type level. -/
theorem curve_preservesTerminalObjects :
    PreservesLimitsOfShape (Discrete PEmpty.{1}) (curveGeometricFiberFunctor K Omega x) :=
  preservesTerminalObjects_typeLevel (S := CurveBase K) (Omega := Omega) (x := x)

/-- Limits of a fixed shape transfer from the Type-valued geometric fiber functor
to the `FintypeCat`-valued lift. -/
theorem preservesLimitsOfShape_of_typeLevel {J : Type*} [Category J]
    (hfin : GeometricFiberFinite K Omega x)
    (h : PreservesLimitsOfShape J (curveGeometricFiberFunctor K Omega x)) :
    PreservesLimitsOfShape J (curveGeometricFiberFunctorFintype K hfin) := by
  haveI h1 : PreservesLimitsOfShape J (curveGeometricFiberFunctor K Omega x) := h
  haveI h2 : PreservesLimitsOfShape J
      (curveGeometricFiberFunctorFintype K hfin ⋙ FintypeCat.incl) := h1
  exact preservesLimitsOfShape_of_comp_of_reflects _ FintypeCat.incl

/-- Colimits of a fixed shape transfer from the Type-valued geometric fiber
functor to the `FintypeCat`-valued lift. -/
theorem preservesColimitsOfShape_of_typeLevel {J : Type*} [Category J]
    (hfin : GeometricFiberFinite K Omega x)
    (h : PreservesColimitsOfShape J (curveGeometricFiberFunctor K Omega x)) :
    PreservesColimitsOfShape J (curveGeometricFiberFunctorFintype K hfin) := by
  haveI h1 : PreservesColimitsOfShape J (curveGeometricFiberFunctor K Omega x) := h
  haveI h2 : PreservesColimitsOfShape J
      (curveGeometricFiberFunctorFintype K hfin ⋙ FintypeCat.incl) := h1
  exact preservesColimitsOfShape_of_comp_of_reflects _ FintypeCat.incl

/-- Preservation of epimorphisms transfers to the `FintypeCat`-valued lift. -/
theorem preservesEpimorphisms_of_typeLevel
    (hfin : GeometricFiberFinite K Omega x)
    (h : Functor.PreservesEpimorphisms (curveGeometricFiberFunctor K Omega x)) :
    Functor.PreservesEpimorphisms (curveGeometricFiberFunctorFintype K hfin) := by
  haveI h1 : Functor.PreservesEpimorphisms (curveGeometricFiberFunctor K Omega x) := h
  haveI h2 : Functor.PreservesEpimorphisms
      (curveGeometricFiberFunctorFintype K hfin ⋙ FintypeCat.incl) := h1
  exact Functor.preservesEpimorphisms_of_preserves_of_reflects _ FintypeCat.incl

/-- Reflection of isomorphisms transfers to the `FintypeCat`-valued lift. -/
theorem reflectsIsomorphisms_of_typeLevel
    (hfin : GeometricFiberFinite K Omega x)
    (h : (curveGeometricFiberFunctor K Omega x).ReflectsIsomorphisms) :
    (curveGeometricFiberFunctorFintype K hfin).ReflectsIsomorphisms := by
  haveI h1 : (curveGeometricFiberFunctor K Omega x).ReflectsIsomorphisms := h
  haveI h2 : (curveGeometricFiberFunctorFintype K hfin ⋙ FintypeCat.incl).ReflectsIsomorphisms := h1
  exact reflectsIsomorphisms_of_comp _ FintypeCat.incl

end Curve

/-! ## 5. The six certificate fields, one theorem each -/

section Fields

variable {K : Type u} [Field K] {Omega : Type u} [Field Omega]
  {x : Spec (CommRingCat.of Omega) ⟶ CurveBase K}

/-- **Item 1 of the certificate, proved unconditionally.** -/
theorem certificate_preservesTerminalObjects
    (hfin : GeometricFiberFinite K Omega x) :
    PreservesLimitsOfShape (Discrete PEmpty.{1})
      (curveGeometricFiberFunctorFintype K hfin) :=
  preservesLimitsOfShape_of_typeLevel hfin
    (curve_preservesTerminalObjects (K := K) (Omega := Omega) (x := x))

/-- **Item 2 of the certificate, isolated.**  The hypothesis is the Type-level
pullback-preservation statement for the geometric fiber functor. -/
theorem certificate_preservesPullbacks
    (hfin : GeometricFiberFinite K Omega x)
    (h : PreservesLimitsOfShape WalkingCospan (curveGeometricFiberFunctor K Omega x)) :
    PreservesLimitsOfShape WalkingCospan
      (curveGeometricFiberFunctorFintype K hfin) :=
  preservesLimitsOfShape_of_typeLevel hfin h

/-- **Item 3 of the certificate, isolated.** -/
theorem certificate_preservesFiniteCoproducts
    (hfin : GeometricFiberFinite K Omega x)
    (h : PreservesFiniteCoproducts (curveGeometricFiberFunctor K Omega x)) :
    PreservesFiniteCoproducts (curveGeometricFiberFunctorFintype K hfin) where
  preserves n := preservesColimitsOfShape_of_typeLevel hfin (h.preserves n)

/-- **Item 4 of the certificate, isolated.** -/
theorem certificate_preservesEpis
    (hfin : GeometricFiberFinite K Omega x)
    (h : Functor.PreservesEpimorphisms (curveGeometricFiberFunctor K Omega x)) :
    Functor.PreservesEpimorphisms (curveGeometricFiberFunctorFintype K hfin) :=
  preservesEpimorphisms_of_typeLevel hfin h

/-- **Item 5 of the certificate, isolated.** -/
theorem certificate_preservesQuotientsByFiniteGroups
    (hfin : GeometricFiberFinite K Omega x)
    (h : forall (A : Type u) [Group A] [Finite A],
      PreservesColimitsOfShape (SingleObj A) (curveGeometricFiberFunctor K Omega x)) :
    forall (A : Type u) [Group A] [Finite A],
      PreservesColimitsOfShape (SingleObj A) (curveGeometricFiberFunctorFintype K hfin) :=
  fun A _ _ => preservesColimitsOfShape_of_typeLevel hfin (h A)

/-- **Item 6 of the certificate, isolated.** -/
theorem certificate_reflectsIsos
    (hfin : GeometricFiberFinite K Omega x)
    (h : (curveGeometricFiberFunctor K Omega x).ReflectsIsomorphisms) :
    (curveGeometricFiberFunctorFintype K hfin).ReflectsIsomorphisms :=
  reflectsIsomorphisms_of_typeLevel hfin h

end Fields

/-! ## 6. The remaining type-level statements, and the certificate -/

section Remaining

variable {K : Type u} [Field K] {Omega : Type u} [Field Omega]
  {x : Spec (CommRingCat.of Omega) ⟶ CurveBase K}

/-- The type-level obligations of the geometric fiber functor which are isolated
in this file.  Each field is stated for the *Type-valued* geometric fiber
functor and corresponds verbatim to a FiberFunctorCertificate field of S2070;
the transfer layer above turns it into the FintypeCat-valued field.  No
inhabitant is asserted. -/
structure RemainingTypeLevel (K : Type u) [Field K] (Omega : Type u) [Field Omega]
    (x : Spec (CommRingCat.of Omega) ⟶ CurveBase K) : Prop where
  /-- (G4) preservation of pullbacks. -/
  preservesPullbacks : PreservesLimitsOfShape WalkingCospan (curveGeometricFiberFunctor K Omega x)
  /-- (G5) preservation of finite coproducts. -/
  preservesFiniteCoproducts : PreservesFiniteCoproducts (curveGeometricFiberFunctor K Omega x)
  /-- (G5) preservation of epimorphisms. -/
  preservesEpis : Functor.PreservesEpimorphisms (curveGeometricFiberFunctor K Omega x)
  /-- (G5) preservation of quotients by finite groups. -/
  preservesQuotientsByFiniteGroups : forall (A : Type u) [Group A] [Finite A],
    PreservesColimitsOfShape (SingleObj A) (curveGeometricFiberFunctor K Omega x)
  /-- (G6) reflection of isomorphisms. -/
  reflectsIsos : (curveGeometricFiberFunctor K Omega x).ReflectsIsomorphisms

/-- **The certificate from the remaining type-level statements.**  Item 1 is
proved unconditionally; items 2-6 are exactly the fields of
RemainingTypeLevel. -/
theorem certificate_of_remaining
    (hfin : GeometricFiberFinite K Omega x)
    (h : RemainingTypeLevel K Omega x) :
    FiberFunctorCertificate (curveGeometricFiberFunctorFintype K hfin) where
  preservesTerminalObjects := certificate_preservesTerminalObjects hfin
  preservesPullbacks := certificate_preservesPullbacks hfin h.preservesPullbacks
  preservesFiniteCoproducts :=
    certificate_preservesFiniteCoproducts hfin h.preservesFiniteCoproducts
  preservesEpis := certificate_preservesEpis hfin h.preservesEpis
  preservesQuotientsByFiniteGroups := fun A _ _ =>
    certificate_preservesQuotientsByFiniteGroups hfin
      h.preservesQuotientsByFiniteGroups A
  reflectsIsos := certificate_reflectsIsos hfin h.reflectsIsos

end Remaining

/-! ## 7. Consumer: the universe-corrected card for the once-punctured curve -/

section Consumer

variable {K : Type u} [Field K] {Omega : Type u} [Field Omega]
  {x : Spec (CommRingCat.of Omega) ⟶ CurveBase K}

open LeanFormal.IUT.XiFPaper.S2081CurveCardM2Actual
open LeanFormal.IUT.XiFPaper.S2073FiniteGroupQuotientActual
open LeanFormal.IUT.XiFPaper.S2080CurveQuotientsTransportActual

/-- **Consumer.**  S2081's s2081_cardV_of_M1_M3 needs exactly the fiber-functor
certificate for curveGeometricFiberFunctorFintype; supplying the remaining
type-level statements and S2080's affine quotient input (M1) yields the
universe-corrected CurveEtaleFundamentalGroupCardV K. -/
theorem curveEtaleFundamentalGroupCardV_realized_of_remaining
    (hM1 : S2073AffineActionCoconeIsColimit (curveCoordinateRing K))
    (hfin : GeometricFiberFinite K Omega x)
    (h : RemainingTypeLevel K Omega x)
    (geomPi : ProfiniteGrp.{u + 1}) (geomConn : Prop) :
    Nonempty (CurveEtaleFundamentalGroupCardV K) :=
  s2081_cardV_of_M1_M3 K hM1 (certificate_of_remaining hfin h) geomPi geomConn

end Consumer

/-! ## 8. The exact state of the five isolated items

### Item 2: preservesPullbacks

Statement (verbatim, RemainingTypeLevel.preservesPullbacks):
PreservesLimitsOfShape WalkingCospan (curveGeometricFiberFunctor K Omega x).

Mathematical content: the geometric fiber of the scheme pullback of two finite
etale covers is the pullback in Type of the two geometric fibers; a compatible
pair of lifts of the geometric point x to the two covers extends uniquely to
the scheme pullback.  The tree already contains the concrete pullback cover
finiteEtaleCoverPullbackCover, its limit cone
finiteEtaleCoverPullbackConeInCover and the limit proof
finiteEtaleCoverPullbackIsLimitInCover (Example36CurveGaloisCategory.lean,
section 2), and Mathlib has
CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone together with
diagramIsoCospan (every WalkingCospan-diagram is a cospan).
The remaining formal work is to show that the image cone is a limit cone in
Type, by the scheme pullback universal property pullback.lift / lift_fst /
lift_snd / hom_ext.  This item is therefore a formalization gap of this file,
not a mathematical gap: no Mathlib object is missing.

### Item 3: preservesFiniteCoproducts

Statement: PreservesFiniteCoproducts (curveGeometricFiberFunctor K Omega x),
i.e. for every n the functor preserves colimits indexed by Discrete (Fin n).
It suffices to prove it for Fin 2 (binary coproducts) and Fin 0 (the initial
object), cf. PreservesFiniteCoproducts.of_preserves_binary_and_initial.

Mathematical content: a lift of the geometric point x to the binary scheme
coproduct lands in exactly one summand.  This uses: Spec Omega is a one-point
space, the underlying space of the binary coproduct is the disjoint union
(Scheme.coprodMk, Scheme.isCompl_range_inl_inr, both in
Mathlib/AlgebraicGeometry/Limits.lean), and the factorization of a scheme
morphism through an open immersion whose range contains the image
(AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift, lift_fac).  All
ingredients exist in Mathlib 4.32.2; what is missing is the gluing lemma "a
morphism from a one-point scheme to a binary coproduct factors through a
summand", and the resulting colimit computation in Type.

### Item 4: preservesEpis

Statement: Functor.PreservesEpimorphisms (curveGeometricFiberFunctor K Omega x).
Equivalently (epimorphisms in Type are surjections): every epimorphism
f : Y ⟶ Z of finite etale covers is surjective on the geometric fiber, i.e.
every lift of x to Z lifts to Y.

The mathematical gap is the classification of epimorphisms in the scheme-side
cover category: for finite etale covers of a connected base the epimorphisms are
the surjective ones, but neither direction is formalized in Mathlib or in the
tree.  (For the field-side category (CommAlgCat.FiniteEtale K)^op this is
S1747.EpiSurjective / S1810EpiSurjectiveDedicatedActual; nothing of the kind
exists scheme-side.)

### Item 5: preservesQuotientsByFiniteGroups

Statement: for every finite group A, the geometric fiber functor preserves
colimits of shape SingleObj A.

This is the fiber-level shadow of the missing PreGaloisCategory field G2
(S2070's CurveQuotientsByFiniteGroups, S2072/S2080): the quotient of a finite
etale cover by a finite group action, and its universal property, do not exist
in Mathlib 4.32.2 nor in the tree.  Even the existence of the colimit
(HasColimitsOfShape (SingleObj A) (FiniteEtaleCover X)) is missing;
preservation cannot be stated before it.

### Item 6: reflectsIsos

Statement: (curveGeometricFiberFunctor K Omega x).ReflectsIsomorphisms: a
morphism f : Y ⟶ Z of finite etale covers whose induced map on geometric
fibers is a bijection is an isomorphism.

The gap is the scheme-theoretic statement "a finite etale morphism which is
bijective on the fiber at one geometric point of a connected base is an
isomorphism", which needs: the fiber cardinality of a finite etale morphism is
locally constant, every connected component of a finite etale cover of the
connected curve dominates the curve, and a finite etale morphism of degree one
is an isomorphism.  None of these is in Mathlib 4.32.2.
-/

/-! ## 9. Axiom audit -/

#print axioms preservesLimitsOfShape_of_comp_of_reflects
#print axioms preservesColimitsOfShape_of_comp_of_reflects
#print axioms isTerminal_obj_of_isTerminal
#print axioms preservesLimit_empty
#print axioms preservesTerminalObjects_typeLevel
#print axioms curve_preservesTerminalObjects
#print axioms certificate_preservesTerminalObjects
#print axioms certificate_preservesPullbacks
#print axioms certificate_preservesFiniteCoproducts
#print axioms certificate_preservesEpis
#print axioms certificate_preservesQuotientsByFiniteGroups
#print axioms certificate_reflectsIsos
#print axioms certificate_of_remaining
#print axioms curveEtaleFundamentalGroupCardV_realized_of_remaining

end LeanFormal.IUT.XiFPaper.S2088FiberFunctorCertificateActual
