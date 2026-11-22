/-
# S1913: toward the compactification of the actual S1726 orbicurve

The D9 cusp is, by S1887/S1896, exactly a compactification stack Z of the
orbicurve together with a representably open immersion X.stack -> Z and a
boundary point of Z outside its image.  S1896 constructed the open immersion
of the identity and proved that it can never be the cusp of a genuine
compactification: at the residue scheme of a boundary point it is essentially
surjective, so the boundary separation condition fails.

This file takes the next concrete instance seriously: the actual S1726
orbicurve

    S1726Orbicurve = the representable etale stack of the affine Weierstrass
                     model  y^2 = x^3 + (61/64) x^2 - (125/64) x  over F',

whose once-punctured elliptic signature has exactly one cusp.  The intended
compactification is the projective closure of the affine model; the missing
cusp is the point at infinity O = (0:1:0), i.e. the puncture.

## What is constructed here

* The precise scheme-level compactification datum
  S1913AffineCompactification: a scheme over F', an open immersion of the
  actual affine model into it, a point at infinity, the separation of that
  point from the image of the open immersion, density of the open image and
  properness of the structure morphism.  This is *not* a fake compactification:
  the disjoint-union type construction is excluded by density (and
  properness).

* From any such datum and the representable-open-immersion property of the
  induced stack map, the actual boundary cusp of S1726Orbicurve:
  S1913BoundaryCusp.  The residue scheme is Spec F', the boundary point is
  the point at infinity, and the separation condition is proved from the
  scheme-level separation, *not* assumed.

## The exact first missing

The first missing datum is the scheme-level compactification recorded by
S1913FirstMissing = S1913AffineCompactification:

* the projective closure P of the affine Weierstrass model of E' over F'
  (equivalently: a proper scheme over Spec F' containing Spec R' as a dense
  open subscheme),
* the open immersion Spec R' -> P of the affine chart,
* the point at infinity O = (0:1:0) : Spec F' -> P,
* the separation O not in the affine chart.

The tree has no such scheme: the analogous frozen card
Example36CurveScheme.CurveProjectiveClosureCard records exactly this gap for
the curve y^2 = x^3 - x, with no inhabitant and no consumer.  (Note that this
Mathlib checkout *does* provide AlgebraicGeometry.Proj, so the projective
closure is constructible in principle from the graded homogeneous coordinate
ring, or by gluing the Z != 0 and Y != 0 affine charts along their overlap;
nothing of the sort exists in the tree and none is fabricated here.)

The second, purely 2-categorical, input is the representable open immersion
S1913RepresentableOpenImmersion of the stack map induced by that scheme open
immersion.  It is the non-identity analogue of S1896IdentityOpenImmersion: the
base change at a scheme point t : T -> P must be the actual schematic fibre
product T x_P Spec R'.  The tree records the corresponding general-cospan
iso-comma stack construction as missing in S1864 (its items (a)-(d)); for
*representable* stacks the same witness is a pointwise construction from the
scheme fibre product, but it is not present in the tree either.  It is named
here, not assumed.

With the two inputs the cusp is unconditional: S1913Cusp_of_inputs.
-/

import tmp.sheaf.xif.paper.S1896BoundaryCuspActual
import tmp.sheaf.xif.paper.S1804IsoCommaPullbackActual
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.Topology.Basic

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1913S1726CompactificationActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1896BoundaryCuspActual
open LeanFormal.IUT.XiFPaper.S1804IsoCommaPullbackActual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.N8Closure.RepresentableStackIsStackConstructed
open LeanFormal.IUT.N8Closure.DiscreteSheafIsStack

/-! ## 1. The scheme-level compactification datum of the actual affine model -/

/-- **The compactification datum of the actual S1726 affine Weierstrass model.**

The scheme is a compactification of S1726AffineOver: the affine model is an
open subscheme (the open immersion openMap), its image is dense, the scheme is
proper over Spec F', and there is a point pointAtInfinity which is not in the
image.  The intended, still missing, inhabitant is the projective closure of
y^2 = x^3 + (61/64) x^2 - (125/64) x with pointAtInfinity = (0:1:0).

This is the exact geometric datum the actual cusp needs at the scheme level;
no projective scheme, no properness proof and no point at infinity is assumed
to exist here. -/
structure S1913AffineCompactification where
  /-- The compactifying scheme over Spec F'. -/
  scheme : SchemeOverField S1726K
  /-- The open immersion of the actual affine model. -/
  openMap : S1726AffineOver ⟶ scheme
  /-- It is an open immersion of schemes. -/
  openImmersion : IsOpenImmersion openMap.left
  /-- The point at infinity (the puncture / cusp). -/
  pointAtInfinity : S1726Base ⟶ scheme
  /-- The point at infinity is not in the image of the affine model. -/
  separation : ∀ (s : S1726Base ⟶ S1726AffineOver),
    s ≫ openMap ≠ pointAtInfinity
  /-- The affine model is dense in the compactification. -/
  dense : DenseRange openMap.left.base
  /-- The compactification is proper over the base. -/
  proper : IsProper scheme.hom

namespace S1913AffineCompactification

variable (C : S1913AffineCompactification)

/-- The representable etale pseudofunctor of a scheme over F'. -/
abbrev S1913Y (T : SchemeOverField S1726K) : EtaleStackPseudofunctor S1726K :=
  schemeRepresentableEtalePseudofunctor S1726K T

/-- **Every representable etale pseudofunctor over F' is an etale stack**
(subcanonicality of the etale topology plus descent for discrete categories). -/
theorem S1913RepresentableIsStack (T : SchemeOverField S1726K) :
    (S1913Y T).IsStack (SchemeOverField.etaleTopology S1726K) := by
  have hP : Presieve.IsSheaf (SchemeOverField.etaleTopology S1726K)
      (yoneda.obj T) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      (representableEtalePresheaf_isSheaf (F := S1726K) T)
  change (discretePseudo (C := SchemeOverField S1726K)
    (yoneda.obj T)).IsStack (SchemeOverField.etaleTopology S1726K)
  exact DiscreteSheafStack.discretePseudo_isStack (P := yoneda.obj T) hP

/-- The compactification stack: the representable etale stack of the
compactifying scheme. -/
noncomputable def S1913CompactificationStack :
    EtaleStackOverField S1726K where
  fiber := S1913Y C.scheme
  isStack := S1913RepresentableIsStack C.scheme

/-- The stack morphism induced by the open immersion of schemes. -/
noncomputable def S1913StackOpenMap :
    S1726Orbicurve.stack.Hom C.S1913CompactificationStack :=
  S1742StrongTransOfHom (F := S1726K) C.openMap

/-- The stack point induced by the point at infinity. -/
noncomputable def S1913BoundaryPoint :
    Pseudofunctor.StrongTrans (S1913Y S1726Base)
      C.S1913CompactificationStack.fiber :=
  S1742StrongTransOfHom (F := S1726K) C.pointAtInfinity

/-- The 2-Yoneda formula for the stack open map at a test section. -/
theorem S1913StackOpenMap_app (s : S1726Base ⟶ S1726AffineOver) :
    (C.S1913StackOpenMap.app
        (LocallyDiscrete.mk (Opposite.op S1726Base))).toFunctor.obj
        (Discrete.mk s) =
      Discrete.mk (s ≫ C.openMap) :=
  S1742App_obj (F := S1726K) C.openMap
    (LocallyDiscrete.mk (Opposite.op S1726Base)) s

/-- The 2-Yoneda formula for the boundary point at the identity section. -/
theorem S1913PointObject :
    OrbicurveFiniteEtaleCover.pointObject S1726Base C.S1913BoundaryPoint =
      Discrete.mk C.pointAtInfinity := by
  rw [OrbicurveFiniteEtaleCover.pointObject]
  show (S1742App (F := S1726K) C.pointAtInfinity
      (LocallyDiscrete.mk (Opposite.op S1726Base))).toFunctor.obj
        (Discrete.mk (𝟙 S1726Base)) = Discrete.mk C.pointAtInfinity
  rw [S1742App_obj, Category.id_comp]

/-- **The point at infinity is a boundary point of the actual orbicurve.**
Every point of the orbicurve over Spec F' maps into the open affine image,
whereas the point at infinity does not, so the two are never isomorphic. -/
theorem S1913Boundary_isBoundary :
    ∀ object : S1726Orbicurve.stack.fiber.obj
        (LocallyDiscrete.mk (Opposite.op S1726Base)),
      IsEmpty
        ((C.S1913StackOpenMap.app
            (LocallyDiscrete.mk (Opposite.op S1726Base))).toFunctor.obj object ≅
          OrbicurveFiniteEtaleCover.pointObject S1726Base C.S1913BoundaryPoint) := by
  intro object
  obtain ⟨s⟩ := object
  refine ⟨fun i => C.separation s ?_⟩
  have hi : ((C.S1913StackOpenMap.app
        (LocallyDiscrete.mk (Opposite.op S1726Base))).toFunctor.obj (Discrete.mk s)).as =
      (OrbicurveFiniteEtaleCover.pointObject S1726Base C.S1913BoundaryPoint).as :=
    Discrete.eq_of_hom i.hom
  rw [S1913StackOpenMap_app C s, S1913PointObject C] at hi
  exact hi

/-- **A compactification in this sense strictly extends the affine model.**
If the open immersion were an isomorphism, the point at infinity would be the
image of a point of the affine model.  The separation field therefore rules out
the degenerate "compactification" equal to the orbicurve itself; this is the
scheme-level shadow of the S1896 identity obstruction. -/
theorem not_isIso (C : S1913AffineCompactification) :
    ¬ IsIso C.openMap := by
  intro h
  haveI : IsIso C.openMap := h
  refine C.separation (C.pointAtInfinity ≫ inv C.openMap) ?_
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- **The actual boundary cusp of S1726Orbicurve from the scheme-level
compactification and the representable-open-immersion property of its stack
map.**  The residue scheme is Spec F', the boundary point is the point at
infinity, and the boundary separation is proved from the scheme-level
separation. -/
noncomputable def S1913BoundaryCusp
    (h : EtaleStackOpenImmersion C.S1913StackOpenMap) :
    OrbicurveBoundaryCusp S1726Orbicurve where
  compactification := C.S1913CompactificationStack
  openMap := C.S1913StackOpenMap
  openImmersion := h
  residueScheme := S1726Base
  point := C.S1913BoundaryPoint
  isBoundary := C.S1913Boundary_isBoundary

/-- **The actual cusp from the compactification datum and the
representable-open-immersion property.** -/
theorem S1913Cusp_of_compactification
    (h : EtaleStackOpenImmersion C.S1913StackOpenMap) :
    Nonempty (OrbicurveBoundaryCusp S1726Orbicurve) :=
  ⟨C.S1913BoundaryCusp h⟩

end S1913AffineCompactification

/-! ## 2. The exact first missing -/

/-- **The exact first missing scheme-level datum**: the actual projective
compactification of the affine Weierstrass model of E', with the point at
infinity outside the affine chart. -/
abbrev S1913FirstMissing : Type 1 := S1913AffineCompactification

/-- The induced representable-open-immersion statement for the stack map of a
compactification datum. -/
def S1913RepresentableOpenImmersion (C : S1913AffineCompactification) : Prop :=
  Nonempty (EtaleStackOpenImmersion C.S1913StackOpenMap)

/-- The cusp is obtained from the two explicitly named inputs. -/
theorem S1913Cusp_of_inputs (C : S1913AffineCompactification)
    (h : EtaleStackOpenImmersion C.S1913StackOpenMap) :
    Nonempty (OrbicurveBoundaryCusp S1726Orbicurve) :=
  C.S1913Cusp_of_compactification h

/-- The first missing datum is not an arbitrary stack: it carries an actual
scheme over F', an actual open immersion of the S1726 affine model, and an
actual point at infinity.  The projections are recorded so that consumers can
inspect the exact geometric content. -/
theorem S1913FirstMissing_spec (C : S1913AffineCompactification) :
    IsOpenImmersion C.openMap.left ∧
      (∀ (s : S1726Base ⟶ S1726AffineOver), s ≫ C.openMap ≠ C.pointAtInfinity) ∧
      DenseRange C.openMap.left.base ∧ IsProper C.scheme.hom :=
  ⟨C.openImmersion, C.separation, C.dense, C.proper⟩

/-! ## 3. Checks and axiom audit -/

#check S1913AffineCompactification
#check S1913AffineCompactification.S1913RepresentableIsStack
#check S1913AffineCompactification.S1913CompactificationStack
#check S1913AffineCompactification.S1913StackOpenMap
#check S1913AffineCompactification.S1913BoundaryPoint
#check S1913AffineCompactification.S1913StackOpenMap_app
#check S1913AffineCompactification.S1913PointObject
#check S1913AffineCompactification.S1913Boundary_isBoundary
#check S1913AffineCompactification.not_isIso
#check S1913AffineCompactification.S1913BoundaryCusp
#check S1913AffineCompactification.S1913Cusp_of_compactification
#check S1913FirstMissing
#check S1913RepresentableOpenImmersion
#check S1913Cusp_of_inputs
#check S1913FirstMissing_spec

#print axioms S1913AffineCompactification.S1913RepresentableIsStack
#print axioms S1913AffineCompactification.S1913PointObject
#print axioms S1913AffineCompactification.S1913Boundary_isBoundary
#print axioms S1913AffineCompactification.not_isIso
#print axioms S1913AffineCompactification.S1913BoundaryCusp
#print axioms S1913Cusp_of_inputs

end LeanFormal.IUT.XiFPaper.S1913S1726CompactificationActual
