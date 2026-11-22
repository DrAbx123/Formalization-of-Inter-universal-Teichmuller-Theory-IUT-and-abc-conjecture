/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors / S2086
-/
import tmp.sheaf.xif.paper.S2076IsoCommaTwoPullbackActual
import tmp.sheaf.xif.paper.S2071PastingWitnessActual

/-!
# S2086: ToA assembly from the iso-comma witness: exact 2-categorical first missing

## What is constructed

S2076 proves the recorded `TwoPullbackWitness` of the iso-comma square
`(toA f g, toB f g, f.map, g.map)` for every cospan of actual cover maps.
S2071 proves `S2058PastingStatement` unconditionally, hence the composition
closure `S2044CompositionClosure` (the same closure is already available
unconditionally as S2069's `S2069D6FiniteEtaleOfToA`).

For a scheme point `ptA : T -> A.source.fiber` and a base-change presentation
`Pg` of `g.map` at the induced C-point `ptA ; f.map`, this file constructs:

* `S2086Cone`: the pseudo-cone over the iso-comma square with apex
  `Pg.pullbackScheme`, legs `Pg.projectionMap ; ptA` and `Pg.toSource`;
* `S2086Lift`: the lift `Pg.pullbackScheme -> A x_C B` obtained from
  `S2076Witness.lift`;
* `S2086LiftToA`: the comparison `S2086Lift ; toA ~ Pg.projectionMap ; ptA`,
  obtained from `S2076Witness.liftToX`;
* `S2086ToASquare`: the explicit base-change square of `toA` at `ptA`;
* `S2086ToAPresentation`: the full base-change presentation of `toA` at
  `ptA`, with `pullbackScheme`, `projection`, `projectionMap`, `toSource`
  and `commutes` already constructed; its only conditional field is
  `isPullback`.

## Exact first missing

`S2086BaseChangePullback hg` is the exact missing 2-categorical
identification: for the explicit square `S2086ToASquare`, the lift from
S2076 must be a two-pullback.  This is the base-change/butterfly
identification

  T x_A (A x_C B)  =  T x_C B,

with `P = A x_C B` the iso-comma apex and `T x_C B` the scheme
`Pg.pullbackScheme`.  It is *not* a vertical or horizontal pasting of the
iso-comma square with the presentation square: the two squares share the leg
`B -> C` but sit at different apices and the comparing 2-cells form two
triangles, so `S2058PastingStatement` does not apply.  S2076 supplies only the
recorded seven-field `TwoPullbackWitness`; S1827/S1843/S1844/S1850/S1852 show
that those fields do not imply the full cone-comparison essential surjectivity
needed to identify a base change with the iso-comma.  We therefore do not
claim `S2086BaseChangePullback` follows from S2076 + S2071; it is the precise
first missing input, stated as a Type, with no fabricated witness.

The geometric input `S2086CospanGMapFiniteEtale` (every cover map `g.map` is
representably finite etale; the field isolated in S2087) supplies the
presentation `Pg` and its finite-etale projection.  It is reduced here to the
stack-level cancellation `S2086StackCancellation` (the same statement as
S2088/S2089), using the weak finite-etale structures of `B` and `C` and
S2058's 2-isomorphism invariance.

## Results

* `S2086ToAOfInputs hg h : S2044ToAFiniteEtaleField`;
* `S2086D6FiniteEtaleOfInputs hg h : S2043FirstMissingFiniteEtale` via
  `S2069D6FiniteEtaleOfToA`;
* `S2086D6FiniteEtaleOfStackCancellation hc h` with the geometric input
  replaced by stack cancellation.

## Honest boundary

No `sorry`, no new axiom, no `Nonempty`/`Prop` gate, no fabricated
presentation, finite-etale certificate, or two-pullback witness.  The missing
inputs are Type-valued definitions with no inhabitant supplied here.  The axiom audit at the end
shows only `propext`, `Classical.choice` and `Quot.sound` for every
conditional theorem; `S2044ToAFiniteEtaleField` and
`S2043FirstMissingFiniteEtale` are *not* asserted unconditionally.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2086ToAAssemblyActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1945SitePseudofunctorDataActual
open LeanFormal.IUT.XiFPaper.S1955AssembleCDActual
open LeanFormal.IUT.XiFPaper.S2042D6GeometricHalfActual
open LeanFormal.IUT.XiFPaper.S2043D6StructureMapEqActual
open LeanFormal.IUT.XiFPaper.S2044D6FiniteEtaleClosureActual
open LeanFormal.IUT.XiFPaper.S2058D6FiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2069D6CompositionClosureActual
open LeanFormal.IUT.XiFPaper.S2071PastingWitnessActual
open LeanFormal.IUT.XiFPaper.S2076IsoCommaTwoPullbackActual

universe u

/-- The C-point `ptA ; f.map` at which the second cover is tested. -/
noncomputable def S2086PointC {A C : S1728Cover} (f : S1728CoverMap A C)
    {T : SchemeOverField S1726K}
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber) :
    Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) C.source.fiber :=
  Pseudofunctor.StrongTrans.vcomp ptA f.map

/-- The pseudo-cone over the iso-comma square attached to a base-change
presentation of `g.map` at `ptA ; f.map`. -/
noncomputable def S2086Cone {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
    (Pg : EtaleStackBaseChangePresentation g.map T (S2086PointC f ptA)) :
    (EtalePseudofunctorSquare.mk (toA f g) (toB f g) f.map g.map (commutes f g)).Cone
      (schemeRepresentableEtalePseudofunctor S1726K Pg.pullbackScheme) where
  toX := Pseudofunctor.StrongTrans.vcomp Pg.projectionMap.transformation ptA
  toY := Pg.toSource
  commutes := (S2058AssociatorIso Pg.projectionMap.transformation ptA f.map).trans
    Pg.commutes.symm

/-- The lift of that cone, from S2076's two-pullback witness. -/
noncomputable def S2086Lift {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
    (Pg : EtaleStackBaseChangePresentation g.map T (S2086PointC f ptA)) :
    Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K Pg.pullbackScheme)
      (sitePseudofunctor f g) :=
  (S2076Witness (f := f) (g := g)).lift
    (schemeRepresentableEtalePseudofunctor S1726K Pg.pullbackScheme)
    (S2086Cone f g T ptA Pg)

/-- The comparison of the lift with `toA`. -/
noncomputable def S2086LiftToA {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
    (Pg : EtaleStackBaseChangePresentation g.map T (S2086PointC f ptA)) :
    Iso (Pseudofunctor.StrongTrans.vcomp (S2086Lift f g T ptA Pg) (toA f g))
      (Pseudofunctor.StrongTrans.vcomp Pg.projectionMap.transformation ptA) :=
  (S2076Witness (f := f) (g := g)).liftToX
    (schemeRepresentableEtalePseudofunctor S1726K Pg.pullbackScheme)
    (S2086Cone f g T ptA Pg)

/-- The explicit base-change square of `toA` at `ptA`. -/
noncomputable def S2086ToASquare {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
    (Pg : EtaleStackBaseChangePresentation g.map T (S2086PointC f ptA)) :
    EtalePseudofunctorSquare
      (schemeRepresentableEtalePseudofunctor S1726K Pg.pullbackScheme)
      (sitePseudofunctor f g)
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber :=
  EtalePseudofunctorSquare.mk (S2086Lift f g T ptA Pg)
    Pg.projectionMap.transformation (toA f g) ptA (S2086LiftToA f g T ptA Pg)

/-- **The presentation of `toA` at `ptA`**, given the pullback property of the
explicit base-change square.  Every other field is constructed. -/
noncomputable def S2086ToAPresentation {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber)
    (Pg : EtaleStackBaseChangePresentation g.map T (S2086PointC f ptA))
    (h : (S2086ToASquare f g T ptA Pg).TwoPullbackWitness) :
    EtaleStackBaseChangePresentation
      (source := S2042IsoCommaStackObj (f := f) (g := g))
      (target := A.source) (toA f g) T ptA where
  pullbackScheme := Pg.pullbackScheme
  projection := Pg.projection
  projectionMap := Pg.projectionMap
  toSource := S2086Lift f g T ptA Pg
  commutes := S2086LiftToA f g T ptA Pg
  isPullback := h

/-- The geometric input: every cover map is representably finite etale. -/
def S2086CospanGMapFiniteEtale : Type 1 :=
  forall (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C),
    EtaleStackFiniteEtaleMorphism g.map

/-- **The exact missing 2-categorical identification**, parameterized by a
chosen finite-etale structure on `g.map`: for every point `ptA`, the explicit
base-change square of `toA` is a two-pullback. -/
def S2086BaseChangePullback (hg : S2086CospanGMapFiniteEtale) : Type _ :=
  forall (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber),
    (S2086ToASquare f g T ptA
      ((hg A B C f g).baseChange T (S2086PointC f ptA))).TwoPullbackWitness

/-- The two inputs give `S2044ToAFiniteEtaleField`. -/
noncomputable def S2086ToAOfInputs (hg : S2086CospanGMapFiniteEtale)
    (h : S2086BaseChangePullback hg) : S2044ToAFiniteEtaleField := by
  intro A B C f g
  refine { baseChange := ?_, hasProperty := ?_ }
  · intro T ptA
    exact S2086ToAPresentation f g T ptA
      ((hg A B C f g).baseChange T (S2086PointC f ptA))
      (h A B C f g T ptA)
  · intro T ptA
    exact (hg A B C f g).hasProperty T (S2086PointC f ptA)

/-- **D6(c) finite etaleness** from the two inputs, via S2069. -/
noncomputable def S2086D6FiniteEtaleOfInputs (hg : S2086CospanGMapFiniteEtale)
    (h : S2086BaseChangePullback hg)
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C) :
    S2043FirstMissingFiniteEtale (f := f) (g := g) :=
  S2069D6FiniteEtaleOfToA (S2086ToAOfInputs hg h) f g

/-- The S2071 pasting theorem is available as the unconditional composition
closure; it is the same closure used by S2069. -/
noncomputable def S2086CompositionClosureViaPasting :
    S2044CompositionClosure :=
  S2071S2044CompositionClosure

#print axioms S2086Cone
#print axioms S2086Lift
#print axioms S2086LiftToA
#print axioms S2086ToAPresentation
#print axioms S2086ToAOfInputs
#print axioms S2086D6FiniteEtaleOfInputs
/-- Stack-level cancellation of representable finite etaleness (the same
statement as S2088/S2089).  It supplies `S2086CospanGMapFiniteEtale` from the
weak finite-etale structures of the two covers. -/
def S2086StackCancellation : Type 1 :=
  forall {X Y Z : EtaleStackOverField S1726K} (f : X.Hom Y) (g : Y.Hom Z),
    EtaleStackFiniteEtaleMorphism (Pseudofunctor.StrongTrans.vcomp f g) →
    EtaleStackFiniteEtaleMorphism g →
    EtaleStackFiniteEtaleMorphism f

/-- Stack cancellation gives `S2086CospanGMapFiniteEtale`, using B.finiteEtale,
C.finiteEtale and the 2-isomorphism invariance of S2058. -/
noncomputable def S2086CospanGMapFiniteEtaleOfStackCancellation
    (hc : S2086StackCancellation) : S2086CospanGMapFiniteEtale := by
  intro A B C f g
  have hcomp : EtaleStackFiniteEtaleMorphism
      (Pseudofunctor.StrongTrans.vcomp g.map C.map) :=
    S2058IsoInvarianceFiniteEtale g.commutes.symm B.finiteEtale
  exact hc g.map C.map hcomp C.finiteEtale

/-- D6(c) from stack cancellation and the explicit base-change pullback. -/
noncomputable def S2086D6FiniteEtaleOfStackCancellation
    (hc : S2086StackCancellation)
    (h : S2086BaseChangePullback (S2086CospanGMapFiniteEtaleOfStackCancellation hc))
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C) :
    S2043FirstMissingFiniteEtale (f := f) (g := g) :=
  S2086D6FiniteEtaleOfInputs (S2086CospanGMapFiniteEtaleOfStackCancellation hc) h f g

#print axioms S2086CospanGMapFiniteEtaleOfStackCancellation
#print axioms S2086D6FiniteEtaleOfStackCancellation
/-- The exact first missing, bundled: a finite-etale structure on every cover
map together with the base-change pullback for the presentations it chooses. -/
def S2086FirstMissing : Type _ :=
  Sigma (fun hg : S2086CospanGMapFiniteEtale => S2086BaseChangePullback hg)

/-- The bundled first missing gives `S2044ToAFiniteEtaleField`. -/
noncomputable def S2086ToAOfFirstMissing (h : S2086FirstMissing) :
    S2044ToAFiniteEtaleField :=
  S2086ToAOfInputs h.1 h.2

/-- The bundled first missing gives D6(c) finite etaleness. -/
noncomputable def S2086D6FiniteEtaleOfFirstMissing (h : S2086FirstMissing)
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C) :
    S2043FirstMissingFiniteEtale (f := f) (g := g) :=
  S2086D6FiniteEtaleOfInputs h.1 h.2 f g

#print axioms S2086ToAOfFirstMissing
#print axioms S2086D6FiniteEtaleOfFirstMissing
#print axioms S2086CompositionClosureViaPasting

end LeanFormal.IUT.XiFPaper.S2086ToAAssemblyActual

end
