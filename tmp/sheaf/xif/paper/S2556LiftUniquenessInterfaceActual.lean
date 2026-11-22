/-
# S2556: lift uniqueness coherence for TwoPullbackWitness

`TwoPullbackWitness` provides lift/liftToX/liftToY/liftTwoCell/twoCell_ext but **no**
lift uniqueness.  This file records the exact missing coherence field and the
consumer chain for S2555ExtractionIso.  It is an interface file, not a fake
witness: no field is inhabited and no axiom is introduced.
-/
import tmp.sheaf.xif.paper.S2555ExtractionTransportActual

noncomputable section
open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2519InvEquivalenceGoalActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2556LiftUniquenessInterfaceActual

universe u
variable {F : Type u} [Field F]

/-- Proposed missing coherence: a two-pullback lift is unique up to a
2-isomorphism among all 1-cells whose composites with the two square legs are
2-isomorphic to the cone's legs. -/
def S2556LiftUniqueness
    {P X Y Z : Iut.EtaleStackPseudofunctor F}
    (sq : Iut.EtalePseudofunctorSquare P X Y Z)
    (w : sq.TwoPullbackWitness) : Prop :=
  ∀ (W : Iut.EtaleStackPseudofunctor F) (c : sq.Cone W)
    (L : Pseudofunctor.StrongTrans W P),
    Iso (Pseudofunctor.StrongTrans.vcomp L sq.toX) c.toX →
    Iso (Pseudofunctor.StrongTrans.vcomp L sq.toY) c.toY →
    Nonempty (L ≅ w.lift W c)

/-- The concrete coherence needed for the identity-point base change square of
an orbicurve cover (consumer S2555ExtractionIso). -/
def S2556IdentityBaseChangeLiftUnique
    (X : Iut.OrbicurveFiniteEtaleCover S2482Orbicurve) : Prop :=
  let bc := X.finiteEtale.baseChange S2482AffineOver S2519BasePoint
  let sq := Iut.EtalePseudofunctorSquare.mk
    bc.toSource bc.projectionMap.transformation X.map S2519BasePoint bc.commutes
  S2556LiftUniqueness sq bc.isPullback

/-! ## Consumers of `S2556LiftUniqueness`

1. `S2555ExtractionIso X S hS`
2. `S2554CanonicalData X S hS`
3. `S2554CanonicalEssSurj`
4. `S2553CorrectedEssSurj`
5. `S2549` / `S2552` unconditional equivalences
6. representable essential surjectivity of `S2519InvFunctor`

Without the coherence, only the section `q ≫ e ≅ id_S` is available from
`bc.isPullback.liftToX`; `twoCell_ext` cannot produce the retraction
`e ≫ q ≅ id_P` because there is no 2-cell between `e ≫ q` and `id_P` from the
recorded fields.
-/

#check S2556LiftUniqueness
#check S2556IdentityBaseChangeLiftUnique
end LeanFormal.IUT.XiFPaper.S2556LiftUniquenessInterfaceActual
end