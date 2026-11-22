/-
# S2558: exposure plan for concrete S2512/S2514 witnesses

Refinement of S2556: the uniqueness field must compare two 1-cells that are
both LIFTS OF THE SAME CONE (with comparison 2-isos), not an arbitrary 1-cell
with only leg isos.  For the extraction argument:
  q := lift (identity cone on TStack S),
  r := lift (identity cone on P),
  e := toSource cast along hS.
Then e ≫ q and r are both lifts of the identity cone on P, hence equal up to
2-iso by lift uniqueness; and r is a lift of the identity cone, as is id_P,
so r ≅ id_P.  Then e ≫ q ≅ id_P, giving the extraction iso.
-/
import tmp.sheaf.xif.paper.S2557LiftUniquenessScopeActual

noncomputable section
open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2556LiftUniquenessInterfaceActual
open LeanFormal.IUT.XiFPaper.S2557LiftUniquenessScopeActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2558ConcreteWitnessPlanActual

universe u
variable {F : Type u} [Field F]

/-- A 1-cell together with comparison 2-isos to a cone's two legs. -/
structure S2558LiftOfCone
    {P X Y Z : Iut.EtaleStackPseudofunctor F}
    (sq : Iut.EtalePseudofunctorSquare P X Y Z)
    {W : Iut.EtaleStackPseudofunctor F} (c : sq.Cone W)
    (L : Pseudofunctor.StrongTrans W P) where
  toX : Iso (Pseudofunctor.StrongTrans.vcomp L sq.toX) c.toX
  toY : Iso (Pseudofunctor.StrongTrans.vcomp L sq.toY) c.toY

/-- The correct lift-uniqueness statement: any two lifts of the same cone are
2-isomorphic. -/
def S2558LiftUnique
    {P X Y Z : Iut.EtaleStackPseudofunctor F}
    (sq : Iut.EtalePseudofunctorSquare P X Y Z)
    (w : sq.TwoPullbackWitness) : Prop :=
  ∀ (W : Iut.EtaleStackPseudofunctor F) (c : sq.Cone W)
    (L1 L2 : Pseudofunctor.StrongTrans W P),
    S2558LiftOfCone sq c L1 →
    S2558LiftOfCone sq c L2 →
    Nonempty (L1 ≅ L2)

/-! ## Exposure plan

### S2512Witness
`S2512Witness` has lift = `S2512Lift hpb W cone` (pointwise pullback lift).
To expose `S2558LiftUnique` for it:
1. prove pointwise equality of two lifts using `hpb.lift` uniqueness;
2. assemble a strong-trans 2-iso via `S2512Val_isoOfValEq`;
3. this is a real proof, but it only applies to squares whose witness is
   `S2512Witness hpb hX hY`.

### S2514IdWitness
`S2514IdWitness` has lift = `cone.toY`, liftTwoCell = `morphism.toY`.
To expose `S2558LiftUnique`:
1. both lifts of the same cone differ by a 2-cell assembled from the cone
   comparison data (unitors);
2. the comparison is determined by the cone's own commutes field;
3. requires the same compatibility data as `S2558LiftOfCone`, not only legs.

### Consumers
`S2555ExtractionIso` → `S2554CanonicalData` → `S2554CanonicalEssSurj`
→ `S2553CorrectedEssSurj` → `S2549/S2552` unconditional equivalences.

### Blocker
`X.finiteEtale.baseChange` is an abstract `TwoPullbackWitness`; it is not
definitionally `S2512Witness` or `S2514IdWitness`.  Applying either exposure
requires replacing/refining the cover's finite-etale data, not merely adding
a lemma.
-/

#check S2558LiftOfCone
#check S2558LiftUnique
end LeanFormal.IUT.XiFPaper.S2558ConcreteWitnessPlanActual
end