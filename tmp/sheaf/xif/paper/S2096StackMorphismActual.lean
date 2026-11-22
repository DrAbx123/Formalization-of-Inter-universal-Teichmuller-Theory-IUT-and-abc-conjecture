import tmp.sheaf.xif.paper.S2092FiniteEtaleStackMorphismActual
import tmp.sheaf.xif.paper.S1742TwoYonedaActual
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# S2096: S2092MorphismOfFiniteEtaleStacks -- reduction and the exact missing
representability/descent API

## The target

'S2092MorphismOfFiniteEtaleStacks' (S2092FiniteEtaleStackMorphismActual) is

    forall (m : X.Hom Y) (y : Y.Hom Z) (x : X.Hom Z),
      Iso (vcomp m y) x -> EtaleStackFiniteEtaleMorphism x ->
      EtaleStackFiniteEtaleMorphism y -> EtaleStackFiniteEtaleMorphism m,

and it is the exact remaining input of the D6(c) chain
S2092 -> S2087GMapFiniteEtaleField -> S2086CospanGMapFiniteEtale ->
S2086D6FiniteEtaleOfInputs.

## What this file proves

1. 'S2096_section_isFinite_etale': a section of a finite etale morphism of
   schemes is finite etale (Mathlib: 'IsClosedImmersion.of_comp',
   'IsSeparated' from 'IsFinite', 'Etale.of_comp').  This is the scheme-level
   property step of the route, in the form in which it is needed: the fibre
   product R = B x_A T sits over B by base change of the section T -> A of the
   finite etale A -> T.
2. 'S2096HomOfVcomp' and 'S2096HomOfSchemeRepresentableMap': the 2-Yoneda
   comparison (S1742) is compatible with vertical composition, and it recovers
   the scheme morphism of a representable scheme map.  These are the comparison
   steps of the route: they turn the 1-cell comparison 'lift ; qy ~ qx' into
   the *equality* 'beta ; qy = qx' of scheme morphisms consumed by the
   scheme-level cancellation 'S2091_scheme_finiteEtale_cancel_special'.
3. The vertex construction (section 4): from a presentation of y at 'ptY ; y'
   (apex A, source vy, projection qy) and a presentation of 'm ; y' at
   'ptY ; y' (apex B, source ux, projection qx), the file constructs the cone
   '(ux ; m, qx)' over the y-presentation square, its lift
   'ell : B -> A' ('S2096VertexLift'), the vertex map 'beta = Hom ell'
   ('S2096VertexMap'), the comparison 2-cells, the vertex square
   '(B -> X, B -> A, m, vy)' ('S2096VertexSquare'), and -- from the
   two-pullback property of that square -- the vertex presentation of m at
   '(A, vy)' ('S2096VertexPresentation').
4. 'S2096VertexProjection_isFiniteEtale': the projection beta : B -> A of that
   vertex presentation is finite etale, by scheme cancellation along
   'beta ; qy = qx' (S2091).
5. 'S2096MorphismOfFiniteEtaleStacks_of_presentationField': the pointwise
   base-change presentation API 'S2096BaseChangePresentationField' gives
   'S2092MorphismOfFiniteEtaleStacks' (complete proof, using
   'S2058IsoInvarianceFiniteEtale' to align 'm ; y' with x).
6. The consequences: 'S2096GMapFiniteEtaleField' (the S2087 field), its cospan
   form, the exact 'S2086CospanGMapFiniteEtale' shape, and D6(c) via
   'S2086D6FiniteEtaleOfInputs' once S2086's butterfly input
   'S2086BaseChangePullback' is available.

## The exact first missing API

The tree cannot construct 'EtaleStackBaseChangePresentation' for a morphism
that is not the 2-Yoneda image of a scheme morphism with representable source
(compare S1896 for the identity and S1926 for an open immersion from a
scheme-level model).  Concretely, two API pieces are missing; both are stated
below as Type-valued definitions, and **neither has an inhabitant**:

* 'S2096UnpastingStatement' -- (M1), right cancellation of the recorded
  two-pullback witness under S2062's pasting, in the *explicit* form needed
  here: the vertex square 'S2096VertexSquare' is a two-pullback.  It is the
  standard converse pasting law for bicategorical pullbacks, and it is true
  geometrically because 'B = X x_Z T = X x_Y (Y x_Z T) = X x_Y A'.  It is not
  derivable from the recorded 'TwoPullbackWitness' fields alone: those have no
  1-cell uniqueness, so the lift of a cone over the pasted square only gives
  'lift ; beta ; qy ~ cone.toY ; qy', and cancelling the representable 1-cell
  qy on the right is false in general.  This is the same boundary recorded by
  S2062 ('TwoPullbackWitness.paste' needs an extra faithfulness input for
  'twoCell_ext'), S2086 ('S2086BaseChangePullback' is not derivable from the
  weak witness), S2090 (postcomposition cancellation is false) and S2094.
* 'S2096BaseChangeStatement' -- (M2), base change of a base-change presentation
  along a finite etale map 's : T -> A' of test schemes:
  'R = Q.pullbackScheme x_A T' with projection 'R -> T' and finite etale
  projection.  The two witnesses are not vertically composable in the sense of
  'EtalePseudofunctorSquare.pasteSquare' (the new square is based on A, the old
  one on Y), so S2062's pasting does not apply.

Given (M1) and (M2), the route to 'S2096BaseChangePresentationField' is:

    vertex presentation of m at (A, vy)            [proved, from (M1)]
    section s : T -> A with s ; vy ~ ptY            [constructible: the cone
                                                    (ptY, id) over the
                                                    y-presentation square]
    s finite etale                                  [proved:
                                                    S2096_section_isFinite_etale
                                                    + s ; qy = id, via
                                                    S2096HomOfVcomp]
    base change of the vertex presentation along s   [missing, (M2)]
    restriction of the point along s ; vy ~ ptY     [missing: iso-invariance of
                                                    EtaleStackBaseChangePresentation
                                                    under an iso of the point;
                                                    S2058 transports only the
                                                    map, not the point]

The last item is a third, purely formal transport that the tree does not have;
it is recorded here in the module prose only, since stating it needs the
point-iso transport of 'EtalePseudofunctorSquare'.  Consequently
'S2096BaseChangePresentationField' is *not* derived here from (M1) and (M2);
it is kept as the headline missing input, and (M1)/(M2) are its precise
decomposition.

## What is NOT claimed

* No inhabitant of 'S2096BaseChangePresentationField',
  'S2096UnpastingStatement', 'S2096BaseChangeStatement' or
  'S2096CancellationStatement' is asserted.
* 'S2092MorphismOfFiniteEtaleStacks' is *not* asserted unconditionally: the
  theorem below is conditional on the missing API.
* No sorry, no new axiom, no 'Nonempty'/'Prop' gate on the conditional
  results; the axiom audit at the end shows only propext,
  Classical.choice and Quot.sound.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2096StackMorphismActual

open CategoryTheory
open AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S2043D6StructureMapEqActual
open LeanFormal.IUT.XiFPaper.S2058D6FiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2086ToAAssemblyActual
open LeanFormal.IUT.XiFPaper.S2087ToAObstructionActual
open LeanFormal.IUT.XiFPaper.S2091SchemeDirectActual
open LeanFormal.IUT.XiFPaper.S2092FiniteEtaleStackMorphismActual

universe u
/-! ## 1. A section of a finite etale morphism is finite etale -/

/-- **Scheme-level section lemma.**  If 's ; f = 1' and f is finite etale,
then s is finite etale.

'Etale f' supplies 'LocallyOfFiniteType f' and 'FormallyUnramified f', so
'Etale s' follows from 'Etale.of_comp'; 'IsFinite f' supplies 'IsSeparated f',
and 1 is a closed immersion, so 'IsClosedImmersion.of_comp' gives
'IsClosedImmersion s', hence 'IsFinite s'.

Geometrically: a section of a finite etale (in particular separated and
unramified) morphism is a clopen immersion. -/
theorem S2096_section_isFinite_etale {X Y : Scheme.{u}} (s : X ⟶ Y) (f : Y ⟶ X)
    [IsFinite f] [Etale f] (h : s ≫ f = 𝟙 X) : IsFinite s ∧ Etale s := by
  haveI : IsSeparated f := inferInstance
  haveI hEt : Etale (s ≫ f) := by rw [h]; infer_instance
  haveI hCl : IsClosedImmersion (s ≫ f) := by rw [h]; infer_instance
  haveI hCls : IsClosedImmersion s := IsClosedImmersion.of_comp s f
  exact ⟨inferInstance, Etale.of_comp s f⟩

#print axioms S2096_section_isFinite_etale

/-! ## 2. The 2-Yoneda comparison is compatible with vertical composition -/

/-- **Composition formula for the 2-Yoneda comparison.**  For strong
transformations 'L : y(S) -> y(T)' and 'M : y(T) -> y(U)' of representable
etale pseudofunctors, the underlying scheme morphism of 'L ; M' is the
composite of the underlying scheme morphisms.

This is the comparison step of the route to S2092: the lift comparison
'lift ; qy ~ qx' of strong transformations is turned into the equality
'beta ; qy = qx' of scheme morphisms, which is what the scheme-level
cancellation 'S2091_scheme_finiteEtale_cancel_special' consumes. -/
theorem S2096HomOfVcomp {S T U : SchemeOverField S1726K}
    (L : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K S)
      (schemeRepresentableEtalePseudofunctor S1726K T))
    (M : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T)
      (schemeRepresentableEtalePseudofunctor S1726K U)) :
    S1742HomOfStrongTrans (Pseudofunctor.StrongTrans.vcomp L M) =
      S1742HomOfStrongTrans L ≫ S1742HomOfStrongTrans M := by
  rw [← S1742HomOfStrongTrans_def (Pseudofunctor.StrongTrans.vcomp L M)]
  rw [show (Pseudofunctor.StrongTrans.vcomp L M).app
        (LocallyDiscrete.mk (Opposite.op S)) =
      L.app (LocallyDiscrete.mk (Opposite.op S)) ≫
        M.app (LocallyDiscrete.mk (Opposite.op S)) from rfl]
  rw [S1742Comp_toFunctor_obj]
  rw [← Discrete.mk_as ((L.app (LocallyDiscrete.mk (Opposite.op S))).toFunctor.obj
    (Discrete.mk (𝟙 S)))]
  rw [S1742HomOfStrongTrans_def L]
  rw [S1742Key M (LocallyDiscrete.mk (Opposite.op S)) (S1742HomOfStrongTrans L)]

#print axioms S2096HomOfVcomp


/-- The 2-Yoneda comparison of a representable scheme map recovers that map. -/
theorem S2096HomOfSchemeRepresentableMap {S T : SchemeOverField S1726K}
    (f : S ⟶ T) (F : SchemeRepresentableMap f) :
    S1742HomOfStrongTrans F.transformation = f := by
  rw [← S1742HomOfStrongTrans_def F.transformation]
  rw [F.app_eq (Opposite.op S)]
  rfl

#print axioms S2096HomOfSchemeRepresentableMap

/-! ## 3. The exact missing base-change presentation API -/

/-- **The exact missing base-change presentation API** (no inhabitant).

For every morphism 'm : X -> Y' and 'y : Y -> Z' of etale stacks over the
D6 field, every scheme point 'ptY : T -> Y', and every pair of base-change
presentations of y and of 'm ; y' at the induced Z-point 'ptY ; y', there
is a base-change presentation of m at ptY whose projection is finite etale.

Mathematically this is the base-change computation
'X x_Y T = (X x_Z T) x_{(Y x_Z T)} T' together with finite etaleness of the
projection; see the module docstring for the decomposition into (M1), (M2) and the point-iso transport.
The tree has no construction of 'EtaleStackBaseChangePresentation' for a
morphism that is not the 2-Yoneda image of a scheme morphism with representable
source (compare S1896 for the identity, S1926 for an open immersion from a
scheme-level model), and the two two-pullback fields it would need are exactly
(M1) and (M2). -/
def S2096BaseChangePresentationField : Type 1 :=
  ∀ {X Y Z : EtaleStackOverField S1726K} (m : X.Hom Y) (y : Y.Hom Z)
    (T : SchemeOverField S1726K)
    (ptY : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) Y.fiber),
    EtaleStackBaseChangePresentation y T
      (Pseudofunctor.StrongTrans.vcomp ptY y) →
    EtaleStackBaseChangePresentation (Pseudofunctor.StrongTrans.vcomp m y) T
      (Pseudofunctor.StrongTrans.vcomp ptY y) →
    Σ' P : EtaleStackBaseChangePresentation m T ptY,
      AlgebraicGeometry.IsFinite P.projection.left ∧
        AlgebraicGeometry.Etale P.projection.left

/-- **(M1), stated for the record**: right cancellation of the recorded
two-pullback witness under S2062's pasting.  From a witness for the lower
square and a witness for the pasted square, a witness for the upper square.

This is the standard converse pasting law for bicategorical pullbacks; it is
*not* provable from the recorded fields of
'EtalePseudofunctorSquare.TwoPullbackWitness' alone (no 1-cell uniqueness), and
it is **not** proved or assumed in this file. -/
def S2096CancellationStatement : Type 1 :=
  ∀ {P B' N M L M' : EtaleStackPseudofunctor S1726K}
    (toX : Pseudofunctor.StrongTrans P B')
    (toY : Pseudofunctor.StrongTrans P N)
    (xToBase : Pseudofunctor.StrongTrans B' M)
    (bottom : EtalePseudofunctorSquare N M L M')
    (commutes : Iso (Pseudofunctor.StrongTrans.vcomp toX xToBase)
      (Pseudofunctor.StrongTrans.vcomp toY bottom.toX)),
    bottom.TwoPullbackWitness →
    (EtalePseudofunctorSquare.pasteSquare toX toY xToBase bottom commutes).TwoPullbackWitness →
    (EtalePseudofunctorSquare.mk toX toY xToBase bottom.toX commutes).TwoPullbackWitness

/-! ## 4. The vertex square, the vertex presentation, and (M1) explicitly -/

section VertexData

variable {X Y Z : EtaleStackOverField S1726K}
variable (m : X.Hom Y) (y : Y.Hom Z)
variable (T : SchemeOverField S1726K)
variable (ptY : Pseudofunctor.StrongTrans
  (schemeRepresentableEtalePseudofunctor S1726K T) Y.fiber)
variable (Py : EtaleStackBaseChangePresentation y T
  (Pseudofunctor.StrongTrans.vcomp ptY y))
variable (Px : EtaleStackBaseChangePresentation (Pseudofunctor.StrongTrans.vcomp m y) T
  (Pseudofunctor.StrongTrans.vcomp ptY y))

/-- The y-presentation square. -/
abbrev S2096SqY : EtalePseudofunctorSquare
    (schemeRepresentableEtalePseudofunctor S1726K Py.pullbackScheme) Y.fiber
    (schemeRepresentableEtalePseudofunctor S1726K T) Z.fiber :=
  EtalePseudofunctorSquare.mk Py.toSource Py.projectionMap.transformation y
    (Pseudofunctor.StrongTrans.vcomp ptY y) Py.commutes

/-- The cone over the y-presentation square built from the x-presentation:
first leg the x-presentation source composed with m, second leg the
x-presentation projection. -/
noncomputable def S2096VertexCone :
    (S2096SqY (y := y) (T := T) (ptY := ptY) Py).Cone
      (schemeRepresentableEtalePseudofunctor S1726K Px.pullbackScheme) where
  toX := Pseudofunctor.StrongTrans.vcomp Px.toSource m
  toY := Px.projectionMap.transformation
  commutes := (S2058AssociatorIso Px.toSource m y).trans Px.commutes

/-- The lift of that cone: a point of the y-presentation apex over the
x-presentation apex. -/
noncomputable def S2096VertexLift :
    Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K Px.pullbackScheme)
      (schemeRepresentableEtalePseudofunctor S1726K Py.pullbackScheme) :=
  Py.isPullback.lift (schemeRepresentableEtalePseudofunctor S1726K Px.pullbackScheme)
    (S2096VertexCone (m := m) (y := y) (T := T) (ptY := ptY) (Py := Py) (Px := Px))

/-- The lift compared with the first leg (the x-presentation source). -/
noncomputable def S2096VertexLiftToX :
    Iso (Pseudofunctor.StrongTrans.vcomp
        (S2096VertexLift (m := m) (y := y) (T := T) (ptY := ptY) (Py := Py) (Px := Px))
        Py.toSource)
      (Pseudofunctor.StrongTrans.vcomp Px.toSource m) :=
  Py.isPullback.liftToX (schemeRepresentableEtalePseudofunctor S1726K Px.pullbackScheme)
    (S2096VertexCone (m := m) (y := y) (T := T) (ptY := ptY) (Py := Py) (Px := Px))

/-- The lift compared with the second leg (the x-presentation projection). -/
noncomputable def S2096VertexLiftToY :
    Iso (Pseudofunctor.StrongTrans.vcomp
        (S2096VertexLift (m := m) (y := y) (T := T) (ptY := ptY) (Py := Py) (Px := Px))
        Py.projectionMap.transformation)
      Px.projectionMap.transformation :=
  Py.isPullback.liftToY (schemeRepresentableEtalePseudofunctor S1726K Px.pullbackScheme)
    (S2096VertexCone (m := m) (y := y) (T := T) (ptY := ptY) (Py := Py) (Px := Px))

/-- The underlying scheme morphism from the x-presentation apex to the
y-presentation apex. -/
noncomputable def S2096VertexMap : Px.pullbackScheme ⟶ Py.pullbackScheme :=
  S1742HomOfStrongTrans
    (S2096VertexLift (m := m) (y := y) (T := T) (ptY := ptY) (Py := Py) (Px := Px))

/-- The comparison of the 2-Yoneda 1-cell of the vertex map with the lift. -/
noncomputable def S2096VertexMapIso :
    Iso (S1742StrongTransOfHom (S2096VertexMap (m := m) (y := y) (T := T)
        (ptY := ptY) (Py := Py) (Px := Px)))
      (S2096VertexLift (m := m) (y := y) (T := T) (ptY := ptY) (Py := Py) (Px := Px)) :=
  S1742StrongTransIsoOfHom
    (S2096VertexLift (m := m) (y := y) (T := T) (ptY := ptY) (Py := Py) (Px := Px))

/-- The commutation 2-cell of the vertex square. -/
noncomputable def S2096VertexCommutes :
    Iso (Pseudofunctor.StrongTrans.vcomp Px.toSource m)
      (Pseudofunctor.StrongTrans.vcomp
        (S1742StrongTransOfHom (S2096VertexMap (m := m) (y := y) (T := T)
          (ptY := ptY) (Py := Py) (Px := Px))) Py.toSource) :=
  (S2096VertexLiftToX (m := m) (y := y) (T := T) (ptY := ptY) (Py := Py) (Px := Px)).symm.trans
    (S2058WhiskerRightIso
      (f := S1742StrongTransOfHom (S2096VertexMap (m := m) (y := y) (T := T)
        (ptY := ptY) (Py := Py) (Px := Px)))
      (f' := S2096VertexLift (m := m) (y := y) (T := T) (ptY := ptY) (Py := Py) (Px := Px))
      (g := Py.toSource)
      (e := S2096VertexMapIso (m := m) (y := y) (T := T) (ptY := ptY) (Py := Py) (Px := Px))).symm

/-- The vertex square: apex the x-presentation apex, first leg the
x-presentation source, second leg the vertex map, over m and the
y-presentation source. -/
noncomputable def S2096VertexSquare : EtalePseudofunctorSquare
    (schemeRepresentableEtalePseudofunctor S1726K Px.pullbackScheme) X.fiber
    (schemeRepresentableEtalePseudofunctor S1726K Py.pullbackScheme) Y.fiber where
  toX := Px.toSource
  toY := S1742StrongTransOfHom (S2096VertexMap (m := m) (y := y) (T := T)
    (ptY := ptY) (Py := Py) (Px := Px))
  xToBase := m
  yToBase := Py.toSource
  commutes := S2096VertexCommutes (m := m) (y := y) (T := T) (ptY := ptY) (Py := Py) (Px := Px)

/-- The vertex map composed with the y-presentation projection is the
x-presentation projection: beta ; qy = qx. -/
theorem S2096VertexMap_comp :
    S2096VertexMap (m := m) (y := y) (T := T) (ptY := ptY) (Py := Py) (Px := Px) ≫
        Py.projection =
      Px.projection := by
  have hc := S1742HomOfStrongTrans_congr
    (S2096VertexLiftToY (m := m) (y := y) (T := T) (ptY := ptY) (Py := Py) (Px := Px))
  rw [S2096HomOfVcomp
      (L := S2096VertexLift (m := m) (y := y) (T := T) (ptY := ptY) (Py := Py) (Px := Px))
      (M := Py.projectionMap.transformation),
    S2096HomOfSchemeRepresentableMap Py.projection Py.projectionMap,
    S2096HomOfSchemeRepresentableMap Px.projection Px.projectionMap] at hc
  exact hc

/-- The vertex presentation of m at the y-presentation apex, given the
two-pullback property of the explicit vertex square. -/
noncomputable def S2096VertexPresentation
    (h : (S2096VertexSquare (m := m) (y := y) (T := T) (ptY := ptY) (Py := Py)
      (Px := Px)).TwoPullbackWitness) :
    EtaleStackBaseChangePresentation m Py.pullbackScheme Py.toSource where
  pullbackScheme := Px.pullbackScheme
  projection := S2096VertexMap (m := m) (y := y) (T := T) (ptY := ptY) (Py := Py) (Px := Px)
  projectionMap :=
    { transformation := S1742StrongTransOfHom (S2096VertexMap (m := m) (y := y)
        (T := T) (ptY := ptY) (Py := Py) (Px := Px))
      app_eq := fun U => rfl }
  toSource := Px.toSource
  commutes := S2096VertexCommutes (m := m) (y := y) (T := T) (ptY := ptY) (Py := Py) (Px := Px)
  isPullback := h

/-- The vertex projection is finite etale, by scheme cancellation along the
y-presentation projection (beta ; qy = qx, S2091). -/
theorem S2096VertexProjection_isFiniteEtale
    (hPy : IsFinite Py.projection.left ∧ Etale Py.projection.left)
    (hPx : IsFinite Px.projection.left ∧ Etale Px.projection.left) :
    IsFinite (S2096VertexMap (m := m) (y := y) (T := T) (ptY := ptY) (Py := Py)
        (Px := Px)).left ∧
      Etale (S2096VertexMap (m := m) (y := y) (T := T) (ptY := ptY) (Py := Py)
        (Px := Px)).left := by
  haveI hfin : IsFinite ((S2096VertexMap (m := m) (y := y) (T := T) (ptY := ptY)
      (Py := Py) (Px := Px) ≫ Py.projection).left) := by
    rw [S2096VertexMap_comp (m := m) (y := y) (T := T) (ptY := ptY) (Py := Py)
      (Px := Px)]
    exact hPx.1
  haveI het : Etale ((S2096VertexMap (m := m) (y := y) (T := T) (ptY := ptY)
      (Py := Py) (Px := Px) ≫ Py.projection).left) := by
    rw [S2096VertexMap_comp (m := m) (y := y) (T := T) (ptY := ptY) (Py := Py)
      (Px := Px)]
    exact hPx.2
  haveI : IsFinite Py.projection.left := hPy.1
  haveI : Etale Py.projection.left := hPy.2
  exact S2091_scheme_finiteEtale_cancel_special
    (S2096VertexMap (m := m) (y := y) (T := T) (ptY := ptY) (Py := Py) (Px := Px)).left
    Py.projection.left

end VertexData

/-- **(M1) in explicit form.**  For every point ptY of Y and every pair of
presentations of y and of m ; y at the induced Z-point, the explicit vertex
square is a two-pullback.

No inhabitant is asserted. -/
def S2096UnpastingStatement : Type 1 :=
  ∀ {X Y Z : EtaleStackOverField S1726K} (m : X.Hom Y) (y : Y.Hom Z)
    (T : SchemeOverField S1726K)
    (ptY : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) Y.fiber)
    (Py : EtaleStackBaseChangePresentation y T
      (Pseudofunctor.StrongTrans.vcomp ptY y))
    (Px : EtaleStackBaseChangePresentation (Pseudofunctor.StrongTrans.vcomp m y) T
      (Pseudofunctor.StrongTrans.vcomp ptY y)),
    (S2096VertexSquare (m := m) (y := y) (T := T) (ptY := ptY) (Py := Py)
      (Px := Px)).TwoPullbackWitness

/-- **(M2), the base-change API**: a base-change presentation can be base
changed along a finite etale map of test schemes.

No inhabitant is asserted. -/
def S2096BaseChangeStatement : Type 1 :=
  ∀ {X Y : EtaleStackOverField S1726K} (m : X.Hom Y)
    {A T : SchemeOverField S1726K} (s : T ⟶ A)
    (vy : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K A) Y.fiber)
    (Q : EtaleStackBaseChangePresentation m A vy),
    IsFinite s.left →
    Etale s.left →
    IsFinite Q.projection.left →
    Etale Q.projection.left →
    Σ' R : EtaleStackBaseChangePresentation m T
        (Pseudofunctor.StrongTrans.vcomp (S1742StrongTransOfHom s) vy),
      IsFinite R.projection.left ∧ Etale R.projection.left

#print axioms S2096VertexCone
#print axioms S2096VertexLift
#print axioms S2096VertexSquare
#print axioms S2096VertexMap_comp
#print axioms S2096VertexPresentation
#print axioms S2096VertexProjection_isFiniteEtale

/-! ## 5. The pointwise API gives S2092MorphismOfFiniteEtaleStacks -/

/-- **The missing API gives the S2092 target.**  For a point ptY of Y, the
presentations of y and of x at the induced Z-point 'ptY ; y' are
'hy.baseChange' and the 2-isomorphism transport (S2058) of 'hx' along
'e : m ; y ~ x'; the field then produces the presentation of m at ptY
together with its finite-etale projection. -/
noncomputable def S2096MorphismOfFiniteEtaleStacks_of_presentationField
    (h : S2096BaseChangePresentationField) :
    S2092MorphismOfFiniteEtaleStacks := by
  intro X Y Z m y x e hx hy
  let hx' : EtaleStackFiniteEtaleMorphism
      (Pseudofunctor.StrongTrans.vcomp m y) :=
    S2058IsoInvarianceFiniteEtale e.symm hx
  refine
    { baseChange := ?_
      hasProperty := ?_ }
  · intro T ptY
    exact (h m y T ptY (hy.baseChange T (Pseudofunctor.StrongTrans.vcomp ptY y))
      (hx'.baseChange T (Pseudofunctor.StrongTrans.vcomp ptY y))).1
  · intro T ptY
    exact (h m y T ptY (hy.baseChange T (Pseudofunctor.StrongTrans.vcomp ptY y))
      (hx'.baseChange T (Pseudofunctor.StrongTrans.vcomp ptY y))).2

#print axioms S2096MorphismOfFiniteEtaleStacks_of_presentationField

/-- **The S2087 field from the missing API.** -/
noncomputable def S2096GMapFiniteEtaleField
    (h : S2096BaseChangePresentationField) : S2087GMapFiniteEtaleField :=
  S2092GMapFiniteEtaleOfMorphismOfFiniteEtaleStacks
    (S2096MorphismOfFiniteEtaleStacks_of_presentationField h)

/-- **The cospan form of the S2087 field.** -/
noncomputable def S2096CospanGMapFiniteEtaleField
    (h : S2096BaseChangePresentationField) : S2087CospanGMapFiniteEtaleField := by
  intro A B C f g
  exact S2096GMapFiniteEtaleField h A B C g

/-- **The exact 'S2086CospanGMapFiniteEtale' input of the D6(c) assembly.** -/
noncomputable def S2096S2086CospanGMapFiniteEtale
    (h : S2096BaseChangePresentationField) : S2086CospanGMapFiniteEtale := by
  intro A B C f g
  exact S2096GMapFiniteEtaleField h A B C g

#print axioms S2096GMapFiniteEtaleField
#print axioms S2096CospanGMapFiniteEtaleField
#print axioms S2096S2086CospanGMapFiniteEtale

/-! ## 6. D6(c) via the missing API and S2086's butterfly input -/

/-- **D6(c) from the missing API.**  The finite-etale certificate of
'structureMap f g = toA f g ; A.map' for every cospan of cover maps, given

* the pointwise base-change presentation API 'S2096BaseChangePresentationField'
  (which supplies 'S2086CospanGMapFiniteEtale'), and
* S2086's butterfly identification 'S2086BaseChangePullback' for the
  presentations chosen by that input. -/
noncomputable def S2096D6FiniteEtale
    (h : S2096BaseChangePresentationField)
    (hpb : S2086BaseChangePullback (S2096S2086CospanGMapFiniteEtale h))
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C) :
    S2043FirstMissingFiniteEtale (f := f) (g := g) :=
  S2086D6FiniteEtaleOfInputs (S2096S2086CospanGMapFiniteEtale h) hpb f g

#print axioms S2096D6FiniteEtale

/-! ## 7. Target-locked checks -/

#check @S2096BaseChangePresentationField
#check @S2096UnpastingStatement
#check @S2096BaseChangeStatement
#check @S2096CancellationStatement
#check @S2096_section_isFinite_etale
#check @S2096HomOfVcomp
#check @S2096HomOfSchemeRepresentableMap
#check @S2096VertexSquare
#check @S2096VertexMap_comp
#check @S2096VertexPresentation
#check @S2096VertexProjection_isFiniteEtale
#check @S2096MorphismOfFiniteEtaleStacks_of_presentationField
#check @S2096GMapFiniteEtaleField
#check @S2096CospanGMapFiniteEtaleField
#check @S2096S2086CospanGMapFiniteEtale
#check @S2096D6FiniteEtale

/-- The reduction is stated for the literal S2092 target, not a variant. -/
example :
    (S2096BaseChangePresentationField → S2092MorphismOfFiniteEtaleStacks) :=
  S2096MorphismOfFiniteEtaleStacks_of_presentationField

end LeanFormal.IUT.XiFPaper.S2096StackMorphismActual

end