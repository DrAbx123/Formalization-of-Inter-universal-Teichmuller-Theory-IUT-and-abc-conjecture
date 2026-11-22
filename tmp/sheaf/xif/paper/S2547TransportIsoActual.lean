/-
# S2541: transport of representable finite etaleness along a 2-isomorphism

Target (the E-family of the S2541 plan): for stack morphisms `f g : W ⟶ Z` over a
field `F`, a 2-isomorphism `e : Iso f g` and a representable finite-etale
structure `hf` on `f`, produce a representable finite-etale structure on `g`.

For every test scheme `T` and point `q : T ⟶ Z` the input presentation
`P := hf.baseChange T q` is reused verbatim on the scheme side:

* `P.pullbackScheme`, `P.projection`, `P.projectionMap`, `P.toSource` are kept;
* the new commutativity 2-cell is `E1 = S2542NewCommutes e P`
  (`toSource ; g ≅ projectionMap ; q`), obtained by whiskering `e` on the left
  and composing with `P.commutes`;
* the finite-etale condition on the projection is `E4 = S2542HasProperty`,
  since the projection itself is literally unchanged.

The only new work is rebuilding the two-pullback witness of the transported
square.  A pseudo-cone over the `g`-square is turned into a pseudo-cone over the
`f`-square by replacing its 2-commutativity cell
`toX ; g ≅ toY ; q` with
`toX ; f ≅ toY ; q`, via `whiskerLeftIso toX e` (E2).  A morphism of
`g`-cones is turned into a morphism of `f`-cones; the compatibility square is
the exchange law of the bicategory of pseudofunctors (E3).  The witness fields
`lift`, `liftToX`, `liftToY`, `liftTwoCell`, `liftTwoCell_toX`,
`liftTwoCell_toY` and `twoCell_ext` are then those of `P.isPullback` at the
transported cones (E5).

No sorry, no new axiom, no `native_decide`.
-/
import tmp.sheaf.xif.paper.S1892PullbackFiniteEtaleActual
import tmp.sheaf.xif.paper.S2542TransportE1E4Actual

noncomputable section
open CategoryTheory
open AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open scoped Bicategory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1892PullbackFiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2542TransportE1E4Actual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2541FiniteEtaleTransportIsoActual

universe u

variable {F : Type u} [Field F]

/-! ## 1. The two squares of the presentation, for `f` and the transported `g` -/

section Square

variable {W Z : Iut.EtaleStackOverField F}
variable {f g : W.Hom Z} (e : Iso f g)
variable {T : Iut.SchemeOverField F}
variable {q : Pseudofunctor.StrongTrans
  (Iut.schemeRepresentableEtalePseudofunctor F T) Z.fiber}
variable (P : Iut.EtaleStackBaseChangePresentation f T q)

/-- The square of the recorded base-change presentation of `f`; this is
definitionally the square of `P.isPullback`. -/
abbrev S2541SquareF : Iut.EtalePseudofunctorSquare
    (Iut.schemeRepresentableEtalePseudofunctor F P.pullbackScheme)
    W.fiber
    (Iut.schemeRepresentableEtalePseudofunctor F T)
    Z.fiber :=
  Iut.EtalePseudofunctorSquare.mk P.toSource P.projectionMap.transformation
    f q P.commutes

/-- The square of the transported base-change presentation of `g`: same scheme
projection and same `toSource`, with the `E1` commutativity 2-cell. -/
abbrev S2541SquareG : Iut.EtalePseudofunctorSquare
    (Iut.schemeRepresentableEtalePseudofunctor F P.pullbackScheme)
    W.fiber
    (Iut.schemeRepresentableEtalePseudofunctor F T)
    Z.fiber :=
  Iut.EtalePseudofunctorSquare.mk P.toSource P.projectionMap.transformation
    g q (S2542NewCommutes e P)

/-! ## 2. E2: transporting pseudo-cones from the `g`-square to the `f`-square -/

/-- E2: a pseudo-cone over the `g`-square is a pseudo-cone over the `f`-square
after replacing its 2-commutativity cell by the whiskered composite along
`e : Iso f g`. -/
noncomputable abbrev S2541TransportCone (A : Iut.EtaleStackPseudofunctor F)
    (cone : Iut.EtalePseudofunctorSquare.Cone (S2541SquareG e P) A) :
    Iut.EtalePseudofunctorSquare.Cone (S2541SquareF P) A where
  toX := cone.toX
  toY := cone.toY
  commutes :=
    (@Bicategory.whiskerLeftIso (Iut.EtaleStackPseudofunctor F) inferInstance
      A W.fiber Z.fiber cone.toX f g e).trans cone.commutes

/-! ## 3. E3: transporting cone morphisms -/

/-- E3: a morphism of pseudo-cones over the `g`-square is a morphism of the
transported pseudo-cones over the `f`-square.  The compatibility square is the
exchange law of the bicategory of pseudofunctors, together with the
compatibility of the given cone morphism. -/
noncomputable def S2541TransportConeMorphism (A : Iut.EtaleStackPseudofunctor F)
    (source target : Iut.EtalePseudofunctorSquare.Cone (S2541SquareG e P) A)
    (m : Iut.EtalePseudofunctorSquare.ConeMorphism (S2541SquareG e P) source target) :
    Iut.EtalePseudofunctorSquare.ConeMorphism (S2541SquareF P)
      (S2541TransportCone e P A source) (S2541TransportCone e P A target) where
  toX := m.toX
  toY := m.toY
  compatibility := by
    show Pseudofunctor.StrongTrans.whiskerRight m.toX f ≫
        (Pseudofunctor.StrongTrans.whiskerLeft target.toX e.hom ≫ target.commutes.hom)
      = (Pseudofunctor.StrongTrans.whiskerLeft source.toX e.hom ≫ source.commutes.hom) ≫
        Pseudofunctor.StrongTrans.whiskerRight m.toY q
    have hex : Pseudofunctor.StrongTrans.whiskerLeft source.toX e.hom ≫
        Pseudofunctor.StrongTrans.whiskerRight m.toX g =
        Pseudofunctor.StrongTrans.whiskerRight m.toX f ≫
          Pseudofunctor.StrongTrans.whiskerLeft target.toX e.hom :=
      @Bicategory.whisker_exchange (Iut.EtaleStackPseudofunctor F) inferInstance
        A W.fiber Z.fiber source.toX target.toX f g m.toX e.hom
    rw [← Category.assoc, ← hex, Category.assoc, m.compatibility, Category.assoc]

/-! ## 4. E5: rebuilding the two-pullback witness -/

/-- E5: the two-pullback witness of the transported square, rebuilt from
`P.isPullback` along the cone transport of E2 and E3.  Every field of the
witness is the corresponding field of `P.isPullback` at the transported cones;
the two `liftTwoCell` coherences and `twoCell_ext` only refer to the unchanged
legs `toSource` and `projectionMap`, so they transfer verbatim. -/
noncomputable def S2541TransportWitness :
    (S2541SquareG e P).TwoPullbackWitness where
  lift A cone := P.isPullback.lift A (S2541TransportCone e P A cone)
  liftToX A cone := P.isPullback.liftToX A (S2541TransportCone e P A cone)
  liftToY A cone := P.isPullback.liftToY A (S2541TransportCone e P A cone)
  liftTwoCell A source target m :=
    P.isPullback.liftTwoCell A (S2541TransportCone e P A source)
      (S2541TransportCone e P A target) (S2541TransportConeMorphism e P A source target m)
  liftTwoCell_toX A source target m :=
    P.isPullback.liftTwoCell_toX A (S2541TransportCone e P A source)
      (S2541TransportCone e P A target) (S2541TransportConeMorphism e P A source target m)
  liftTwoCell_toY A source target m :=
    P.isPullback.liftTwoCell_toY A (S2541TransportCone e P A source)
      (S2541TransportCone e P A target) (S2541TransportConeMorphism e P A source target m)
  twoCell_ext A first second alpha beta hX hY :=
    P.isPullback.twoCell_ext A alpha beta hX hY

/-! ## 5. The transported presentation -/

/-- The base-change presentation of `g` at `(T, q)`: the scheme side
(`pullbackScheme`, `projection`, `projectionMap`, `toSource`) is reused from
`P`, the commutativity is `E1` and the pullback witness is E5. -/
noncomputable def S2541TransportPresentation :
    Iut.EtaleStackBaseChangePresentation g T q where
  pullbackScheme := P.pullbackScheme
  projection := P.projection
  projectionMap := P.projectionMap
  toSource := P.toSource
  commutes := S2542NewCommutes e P
  isPullback := S2541TransportWitness e P

end Square

/-! ## 6. The transport theorem -/

/-- **S2541FiniteEtaleTransportIso**: representable finite etaleness of a stack
morphism over a field is invariant under 2-isomorphism of the morphism. -/
noncomputable def S2541FiniteEtaleTransportIso
    {W Z : Iut.EtaleStackOverField F} {f g : W.Hom Z}
    (e : Iso f g) (hf : Iut.EtaleStackFiniteEtaleMorphism f) :
    Iut.EtaleStackFiniteEtaleMorphism g where
  baseChange T q := S2541TransportPresentation e (hf.baseChange T q)
  hasProperty T q := hf.hasProperty T q

/-- The `Nonempty` form of the transport theorem (the statement recorded as
`S1892TransportHolds` in the S1892 dependency file). -/
theorem S2541FiniteEtaleTransportNonempty
    {W Z : Iut.EtaleStackOverField F} {f g : W.Hom Z}
    (e : Iso f g) (hf : Nonempty (Iut.EtaleStackFiniteEtaleMorphism f)) :
    Nonempty (Iut.EtaleStackFiniteEtaleMorphism g) :=
  hf.map (S2541FiniteEtaleTransportIso e)

/-- S1892's transport input is now a theorem. -/
theorem S2541TransportHolds : S1892TransportHolds :=
  fun e hf => S2541FiniteEtaleTransportNonempty e hf

/-! ## 7. Consumer: the S1892 reduction with its transport input discharged -/

open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
  LeanFormal.IUT.XiFPaper.S1864GeneralPullbackStackActual in
/-- Consumer check: `S1892StructureMapIffComposite` asked for
`S1892TransportHolds`; that input is now the theorem `S2541TransportHolds`, so the
recorded structure map of an S1864 iso-comma apex is finite etale exactly when
the composite `toA ; A.map` is. -/
theorem S2541StructureMapIffComposite
    {A B C : S1728Cover} {f : S1728CoverMap A C} {g : S1728CoverMap B C}
    (D : S1864IsoCommaStackObligation f g) :
    Nonempty (Iut.EtaleStackFiniteEtaleMorphism D.structureMap) ↔
      Nonempty (Iut.EtaleStackFiniteEtaleMorphism
        (Pseudofunctor.StrongTrans.vcomp D.toA A.map)) :=
  S1892StructureMapIffComposite S2541TransportHolds D

/-! ## 8. Checks and axiom audit -/

#check @S2541TransportCone
#check @S2541TransportConeMorphism
#check @S2541TransportWitness
#check @S2541TransportPresentation
#check @S2541FiniteEtaleTransportIso
#check @S2541FiniteEtaleTransportNonempty
#check @S2541TransportHolds
#check @S2541StructureMapIffComposite

#print axioms S2541TransportConeMorphism
#print axioms S2541TransportWitness
#print axioms S2541TransportPresentation
#print axioms S2541FiniteEtaleTransportIso
#print axioms S2541FiniteEtaleTransportNonempty
#print axioms S2541TransportHolds
#print axioms S2541StructureMapIffComposite

end LeanFormal.IUT.XiFPaper.S2541FiniteEtaleTransportIsoActual
end