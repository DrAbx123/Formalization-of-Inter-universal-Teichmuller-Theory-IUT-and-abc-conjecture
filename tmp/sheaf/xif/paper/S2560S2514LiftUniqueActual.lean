/-
# S2560: lift uniqueness for the concrete S2514 identity finite-etale witness

The refinement plan `S2559ConcreteWitnessRefinementPlanActual` isolates the
missing coherence `S2559HasLiftUnique` for a finite-etale morphism of etale
stacks: for every scheme-valued point the `S2558LiftUnique` property of the
resulting base-change square must hold.  This file discharges it for

* the concrete witness `S2514IdentityFiniteEtale` of the S2482 orbicurve
  `S2482Orbicurve` (over the concrete field `F = S2480QiActual.F`), whose
  base change at `(T, q)` is `S2514IdBaseChange T q`, and
* the concrete two-pullback witness `S2514IdWitness T q`, whose lift is the
  cone's second leg `cone.toY` and whose `liftTwoCell` is `morphism.toY`.

The mathematical content is the unitariness of the second leg: in the identity
base-change square the vertical leg `sq.toY` is the identity strong
transformation.  For a lift `L` of a cone `c` the `S2558LiftOfCone` data gives
a 2-isomorphism `L vcomp sq.toY ~= c.toY`; the right unitor identifies
`L vcomp id` with `L`.  Hence every lift of `c` is 2-isomorphic to `c.toY`,
and in particular any two lifts of `c` are 2-isomorphic.  This is the
criterion `S2560LiftUnique_of_toY_id`, which does not depend on the particular
`TwoPullbackWitness`, and it is applied to the S2514 witness below.

This closes `S2559HasLiftUnique` for the identity cover; it does not claim the
property for an arbitrary abstract finite-etale morphism (where the second leg
of a base-change square need not be the identity).
-/
import tmp.sheaf.xif.paper.S2559ConcreteWitnessRefinementPlanActual
import tmp.sheaf.xif.paper.S2514IdentityFiniteEtaleActual

noncomputable section
open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2558ConcreteWitnessPlanActual
open LeanFormal.IUT.XiFPaper.S2559ConcreteWitnessRefinementPlanActual
open LeanFormal.IUT.XiFPaper.S2514IdentityFiniteEtaleActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2560S2514LiftUniqueActual

/-! ## 1. The unitor criterion for an identity vertical leg

If the second leg of a square is the identity strong transformation, then any
two `S2558LiftOfCone` structures over the same cone give 2-isomorphic lifts.
No property of the `TwoPullbackWitness` is used: this is a general criterion
for identity-leg squares. -/

section IdentityLeg

universe u
variable {F : Type u} [Field F]

/-- Lift uniqueness for squares whose vertical (`toY`) leg is the identity.
For a cone `c` and a lift `L`, the cone comparison
`L vcomp sq.toY ~= c.toY` becomes `L vcomp id ~= c.toY`, so the right unitor
turns `L` into `c.toY`; two such comparisons therefore compose to `L1 ~= L2`. -/
theorem S2560LiftUnique_of_toY_id
    {P X Z : Iut.EtaleStackPseudofunctor F}
    (sq : Iut.EtalePseudofunctorSquare P X P Z)
    (hY : sq.toY = Pseudofunctor.StrongTrans.id P)
    (w : sq.TwoPullbackWitness) :
    S2558LiftUnique sq w := by
  intro W c L1 L2 h1 h2
  have e1 : Iso (Pseudofunctor.StrongTrans.vcomp L1 (Pseudofunctor.StrongTrans.id P)) c.toY :=
    hY ▸ h1.toY
  have e2 : Iso (Pseudofunctor.StrongTrans.vcomp L2 (Pseudofunctor.StrongTrans.id P)) c.toY :=
    hY ▸ h2.toY
  exact ⟨(Pseudofunctor.StrongTrans.rightUnitor L1).symm.trans
    (e1.trans (e2.symm.trans (Pseudofunctor.StrongTrans.rightUnitor L2)))⟩

end IdentityLeg

/-! ## 2. The concrete identity base-change square -/

/-- The base-change square of the identity finite-etale morphism at the
scheme-valued point `q`, in the shape used by `S2559HasLiftUnique`. -/
noncomputable abbrev S2560S2514Square
    (T : Iut.SchemeOverField F)
    (q : Pseudofunctor.StrongTrans (S2514Y T) S2482Orbicurve.stack.fiber) :
    Iut.EtalePseudofunctorSquare (S2514Y T) S2482Orbicurve.stack.fiber
      (S2514Y T) S2482Orbicurve.stack.fiber :=
  Iut.EtalePseudofunctorSquare.mk q (Pseudofunctor.StrongTrans.id (S2514Y T))
    (Pseudofunctor.StrongTrans.id S2482Orbicurve.stack.fiber) q (S2514IdCommutes T q)

/-- The base change of the concrete identity finite-etale structure is the
concrete S2514 base change, definitionally. -/
theorem S2560S2514BaseChange (T : Iut.SchemeOverField F)
    (q : Pseudofunctor.StrongTrans (S2514Y T) S2482Orbicurve.stack.fiber) :
    S2514IdentityFiniteEtale.baseChange T q = S2514IdBaseChange T q :=
  rfl

/-- The lift of `S2514IdWitness` is the cone's second leg. -/
theorem S2560S2514IdWitness_lift
    (T : Iut.SchemeOverField F)
    (q : Pseudofunctor.StrongTrans (S2514Y T) S2482Orbicurve.stack.fiber)
    (W : Iut.EtaleStackPseudofunctor F) (c : (S2560S2514Square T q).Cone W) :
    (S2514IdWitness T q).lift W c = c.toY :=
  rfl

/-- The 2-cell part of `S2514IdWitness` is the cone morphism's second leg. -/
theorem S2560S2514IdWitness_liftTwoCell
    (T : Iut.SchemeOverField F)
    (q : Pseudofunctor.StrongTrans (S2514Y T) S2482Orbicurve.stack.fiber)
    (W : Iut.EtaleStackPseudofunctor F)
    (source target : (S2560S2514Square T q).Cone W)
    (morphism : (S2560S2514Square T q).ConeMorphism source target) :
    (S2514IdWitness T q).liftTwoCell W source target morphism = morphism.toY :=
  rfl

/-- The concrete S2514 identity witness has lift uniqueness. -/
theorem S2560S2514IdWitnessLiftUnique
    (T : Iut.SchemeOverField F)
    (q : Pseudofunctor.StrongTrans (S2514Y T) S2482Orbicurve.stack.fiber) :
    S2558LiftUnique (S2560S2514Square T q) (S2514IdWitness T q) :=
  S2560LiftUnique_of_toY_id (S2560S2514Square T q) rfl (S2514IdWitness T q)

/-! ## 3. The S2559 predicate for the concrete identity cover -/

/-- `S2559HasLiftUnique` holds for the concrete identity finite-etale morphism
of the S2482 orbicurve: every base change is the S2514 identity square, whose
lift uniqueness is `S2560S2514IdWitnessLiftUnique`. -/
theorem S2560S2514LiftUnique :
    S2559HasLiftUnique (map := Pseudofunctor.StrongTrans.id S2482Orbicurve.stack.fiber)
      S2514IdentityFiniteEtale := by
  intro T q
  exact S2560S2514IdWitnessLiftUnique T q

/-- The consumer-facing form: the terminal identity cover carries the
`S2559HasLiftUnique` hypothesis for its concrete finite-etale structure. -/
theorem S2560S2514TerminalCoverLiftUnique :
    S2559HasLiftUnique (map := Pseudofunctor.StrongTrans.id S2482Orbicurve.stack.fiber)
      S2514TerminalCover.finiteEtale :=
  S2560S2514LiftUnique

end LeanFormal.IUT.XiFPaper.S2560S2514LiftUniqueActual
end
