/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

import Iut.Foundations.Orbicurve
import Mathlib.Tactic

/-!
# IUT I Definition 3.1(d): the degenerate (terminal) etale stack over a field

Frozen scope (2026-10-17, D6 orbicurve instantiation attack, `estimates-rec8` item 23).

## What this file proves

The foundation file `Iut.Foundations.Orbicurve` defines
`EtaleStackOverField F`: a category-valued etale stack over `Spec F`, i.e. a
pseudofunctor `LocallyDiscrete (SchemeOverField F)^op` to `Cat` satisfying
mathlib's effective-descent predicate `Pseudofunctor.IsStack`, with an
optional certified orbicurve signature.  Before this file no inhabitant of
that structure existed in the tree; the audit note in
`HodgeTheater/SourceClauseAssemblyUnitsReduction.lean` records: "No
construction of `EtaleStackOverField` is present in the tree ... Mathlib
carries only the bare class `Pseudofunctor.IsStack`".

This file constructs the *degenerate* inhabitant: the constant pseudofunctor
taking every `U` in `(SchemeOverField F)^op` to the one-object terminal
category `Discrete PUnit` inside `Cat.{u, u}`.  The stack property is proved
through mathlib's own interface: for a covering sieve the functor
`toDescentData` has subsingleton hom types (all homs live in the discrete
category) and nonempty hom types, hence is faithful, full and essentially
surjective; `Pseudofunctor.isStackFor_ofArrows_iff` converts this into
`IsStackFor`, and `Pseudofunctor.IsStack.of_isStackFor` assembles
`fiber.IsStack (SchemeOverField.etaleTopology F)`.

## What this file explicitly does NOT do

* The fibre is constant: it does not depend on `U`, and carries no curve,
  no punctured curve, no cover, and no structure group.  It is a surrogate
  at the structural layer only; it is *not* the K-core orbicurve
  `C_K = C_F x_F K` of IUT I, Definition 3.1(d) (corpus lines 3185-3215).
* Its `orbicurveSignature` is `none`, and this file proves that the
  terminal stack carries no `OrbicurveGeometry` certificate
  (`terminalConstantEtaleStack_no_geometry`); consequently it can never be
  the `stack` field of a `HyperbolicOrbicurve F`
  (`terminalConstantEtaleStack_not_hyperbolicOrbicurve_carrier`).
* No `SourceOrbicurveClause` is manufactured: the D9 orbicurve slot and the
  D6 gate consume a clause whose content is fixed by the constructor layer
  (`SourceClauseConstructors.ofFundamentalGroup`), which requires an actual
  `HyperbolicOrbicurve` together with certified etale fundamental groups.
  Supplying a degenerate clause would close the gate `D6OrbicurveConstruction`
  without any source content, which the project discipline forbids.

## Consumer-side contract (frozen)

* Gate (`SourceDefinition31RootLemmas.lean:5160`):
  `D6OrbicurveConstruction l := forall A : InitialThetaArithmeticData l,
  Nonempty SourceOrbicurveClause` - the clause type has no parameter
  depending on `A`, so the gate carries no arithmetic link to the input.
* D9 slot (`SourceDefinition31D4D9Supply.lean:198`, `orbicurve : Prop` at
  `:203`): the orbicurve slot is an opaque `(Prop, proof)` pair.
* Entry point (`SourceDefinition31PlacePartition.lean:180`, clause argument
  at `:183`): `d11EntryData` takes `(O : SourceOrbicurveClause)` and
  `(orbCompat : Prop) (horbCompat : orbCompat)`; no field of `O` is
  inspected.  The minimal consumer demand is therefore value-level: an
  opaque clause plus an opaque compatibility proposition.  Faithfulness of
  the clause's *content* is enforced only at the constructor layer
  (`SourceClauseConstructors.ofFundamentalGroup`,
  `exactSequenceOfFundamentalGroup`), whose inputs are an actual
  `HyperbolicOrbicurve F` and certified etale fundamental groups
  (`Iut.OrbicurveEtaleFundamentalGroup`); no compiled supplier provides
  those inputs from arithmetic data `A` alone.

## Paper anchor

IUT I, Definition 3.1(d) (corpus `Inter-universal Teichmuller Theory I.txt`,
lines 3185-3215): "C_K is a hyperbolic orbicurve of type (1,l-tors)^pm over K,
with K-core ... given by C_K = C_F x_F K ... C_K determines, up to
K-isomorphism, a hyperbolic orbicurve X_K of type (1,l-tors) over K, together
with natural cartesian diagrams ... of finite etale coverings of hyperbolic
orbicurves and corresponding open immersions of profinite groups. Finally ...
Delta_C has uniquely determined open subgroups ..."
The clause fields (`SourceDefinition31Boundary.lean:445`:
`curve`/`puncturedCurve`/`cover`/`structureGroup`/`cover_surjective`/
`exactSequence`/`cuspCount`/`curveCompatibility`) are a *signature shell*
for this content; the shell is inhabitable by degenerate data, while the
source object itself remains missing (`IUT-I.definition-3.1-D9-orbicurve-slot`,
PARK; report section 15 of `logs/coordination/estimates-rec8-h1-review-20261016.md`).
-/

namespace LeanFormal.IUT

namespace InitialThetaSource

namespace Definition31OrbicurveInstance

open CategoryTheory
open scoped CategoryTheory.Bicategory

universe u v

/-- The constant functor to the one-object terminal category `Discrete PUnit.{u+1}`
inside `Cat.{u, u}`. -/
noncomputable def terminalConstantFiberFunctor (F : Type u) [CommRing F] :
    (Iut.SchemeOverField F)ᵒᵖ ⥤ Cat.{u, u} where
  obj _ := Cat.of (Discrete PUnit.{u+1})
  map _ := 𝟙 _
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The degenerate etale-stack fibre: the constant pseudofunctor at the terminal
category. -/
noncomputable def terminalConstantFiber (F : Type u) [CommRing F] :
    LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ ⥤ᵖ Cat.{u, u} :=
  (terminalConstantFiberFunctor F).toPseudofunctor'

/-- Descent data morphisms over the terminal fibre are subsingletons. -/
instance terminalConstantFiberDescentDataHomSubsingleton (F : Type u) [CommRing F]
    {ι : Type v} {S : Iut.SchemeOverField F} {X : ι → Iut.SchemeOverField F}
    (f : ∀ i, X i ⟶ S) (D₁ D₂ : (terminalConstantFiber F).DescentData f) :
    Subsingleton (D₁ ⟶ D₂) :=
  ⟨fun φ ψ =>
    Pseudofunctor.DescentData.hom_ext fun i =>
      @Subsingleton.elim _ (Discrete.instSubsingletonDiscreteHom _ _) (φ.hom i) (ψ.hom i)⟩

theorem terminalConstantFiber_toDescentData_faithful (F : Type u) [CommRing F]
    {ι : Type v} {S : Iut.SchemeOverField F} {X : ι → Iut.SchemeOverField F}
    (f : ∀ i, X i ⟶ S) :
    ((terminalConstantFiber F).toDescentData f).Faithful :=
  ⟨fun {U V} φ ψ _ =>
    @Subsingleton.elim _ (Discrete.instSubsingletonDiscreteHom U V) φ ψ⟩

theorem terminalConstantFiber_toDescentData_full (F : Type u) [CommRing F]
    {ι : Type v} {S : Iut.SchemeOverField F} {X : ι → Iut.SchemeOverField F}
    (f : ∀ i, X i ⟶ S) :
    ((terminalConstantFiber F).toDescentData f).Full :=
  ⟨fun {U V} g =>
    ⟨(ULift.up (PLift.up (Subsingleton.elim U.as V.as)) : U ⟶ V),
      Subsingleton.elim _ g⟩⟩

theorem terminalConstantFiber_toDescentData_essSurj (F : Type u) [CommRing F]
    {ι : Type v} {S : Iut.SchemeOverField F} {X : ι → Iut.SchemeOverField F}
    (f : ∀ i, X i ⟶ S) :
    ((terminalConstantFiber F).toDescentData f).EssSurj where
  mem_essImage _ :=
    ⟨(Discrete.mk PUnit.unit : Discrete PUnit.{u+1}), ⟨{
      hom := {
        hom := fun _ => ULift.up (PLift.up (Subsingleton.elim _ _))
        comm := fun _ _ _ _ _ _ _ _ =>
          @Subsingleton.elim _ (Discrete.instSubsingletonDiscreteHom _ _) _ _ }
      inv := {
        hom := fun _ => ULift.up (PLift.up (Subsingleton.elim _ _))
        comm := fun _ _ _ _ _ _ _ _ =>
          @Subsingleton.elim _ (Discrete.instSubsingletonDiscreteHom _ _) _ _ }
      hom_inv_id := Subsingleton.elim _ _
      inv_hom_id := Subsingleton.elim _ _ }⟩⟩

theorem terminalConstantFiber_toDescentData_isEquivalence (F : Type u) [CommRing F]
    {ι : Type v} {S : Iut.SchemeOverField F} {X : ι → Iut.SchemeOverField F}
    (f : ∀ i, X i ⟶ S) :
    ((terminalConstantFiber F).toDescentData f).IsEquivalence :=
  ⟨terminalConstantFiber_toDescentData_faithful F f,
   terminalConstantFiber_toDescentData_full F f,
   terminalConstantFiber_toDescentData_essSurj F f⟩

theorem terminalConstantFiber_isStackFor_ofArrows (F : Type u) [CommRing F]
    {ι : Type v} {S : Iut.SchemeOverField F} {X : ι → Iut.SchemeOverField F}
    (f : ∀ i, X i ⟶ S) :
    (terminalConstantFiber F).IsStackFor (Presieve.ofArrows X f) :=
  (Pseudofunctor.isStackFor_ofArrows_iff (F := terminalConstantFiber F) f).2
    (terminalConstantFiber_toDescentData_isEquivalence F f)

theorem terminalConstantFiber_isStack (F : Type u) [CommRing F] :
    (terminalConstantFiber F).IsStack (Iut.SchemeOverField.etaleTopology F) :=
  Pseudofunctor.IsStack.of_isStackFor fun S R hR => by
    rw [← Presieve.ofArrows_category R.arrows]
    exact terminalConstantFiber_isStackFor_ofArrows F (fun (f : R.arrows.category) ↦ f.obj.hom)

/-- The degenerate etale stack over `F` with constant terminal fibre. -/
noncomputable def terminalConstantEtaleStack (F : Type u) [CommRing F] :
    Iut.EtaleStackOverField F :=
  { fiber := terminalConstantFiber F, isStack := terminalConstantFiber_isStack F }

@[simp] theorem terminalConstantEtaleStack_fiber (F : Type u) [CommRing F] :
    (terminalConstantEtaleStack F).fiber = terminalConstantFiber F := rfl

@[simp] theorem terminalConstantEtaleStack_signature_eq_none (F : Type u) [CommRing F] :
    (terminalConstantEtaleStack F).orbicurveSignature = none := rfl

/-- The degenerate stack carries no certified orbicurve geometry: a geometry
certificate would force `orbicurveSignature = some _`, but it is `none`. -/
theorem terminalConstantEtaleStack_no_geometry (F : Type u) [Field F] :
    ¬ Nonempty (Iut.OrbicurveGeometry (terminalConstantEtaleStack F)) := by
  rintro ⟨g⟩
  have h := g.realizes_signature
  rw [terminalConstantEtaleStack_signature_eq_none] at h
  cases h

/-- Consequently the degenerate stack cannot be the carrier of a hyperbolic
orbicurve: no `HyperbolicOrbicurve F` has it as its `stack` field. -/
theorem terminalConstantEtaleStack_not_hyperbolicOrbicurve_carrier (F : Type u) [Field F]
    (X : Iut.HyperbolicOrbicurve F) (h : X.stack = terminalConstantEtaleStack F) : False :=
  terminalConstantEtaleStack_no_geometry F
    ⟨h ▸ X.geometry⟩

/-- A category-valued etale stack over `F` exists in the tree, in the degenerate
structural sense made precise above. -/
theorem etaleStackOverField_nonempty (F : Type u) [CommRing F] :
    Nonempty (Iut.EtaleStackOverField F) :=
  ⟨terminalConstantEtaleStack F⟩

end Definition31OrbicurveInstance

end InitialThetaSource

end LeanFormal.IUT
