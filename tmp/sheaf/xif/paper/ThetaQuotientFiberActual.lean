import tmp.sheaf.xif.paper.ThetaQuotientTotalActual

/-!
# Actual fiber/action data for the quotient theta line bundle

This file continues ThetaQuotientTotalActual. The fiber of the quotient total
bundle over a period base point is the actual L-fiber

  thetaQuotientFiber D b = L,

and its local trivialization is the actual identity equivalence with L. The
period action on the fiber is multiplication by the actual automorphy factor

  thetaFiberAction D U a c = thetaAutomorphyFactor D a (U : L) * c.

The action is proved multiplicative and unital, and the quotient section
satisfies the actual section transformation law on representatives.

No source curve comparison or inequality is asserted.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ABCBridge.ThetaQuotientFiberActual

open LeanFormal.IUT.Foundations.Theta

universe u

/-- Local trivialization of the actual fiber over a period base point. -/
def thetaQuotientFiberTrivialization {L : Type u} [NormedField L]
    [IsUltrametricDist L] [CompleteSpace L]
    (D : ThetaPeriodData L) (b : thetaPeriodBase D) :
    thetaQuotientFiber D b ≃ L :=
  Equiv.refl L

/-- The actual period action on the fiber over the cover representative U. -/
def thetaFiberAction {L : Type u} [NormedField L]
    [IsUltrametricDist L] [CompleteSpace L]
    (D : ThetaPeriodData L) (U : Lˣ) (a : ℤ) (c : L) : L :=
  thetaAutomorphyFactor D a (U : L) * c

/-- The fiber action at exponent zero is the identity. -/
theorem thetaFiberAction_zero {L : Type u} [NormedField L]
    [IsUltrametricDist L] [CompleteSpace L]
    (D : ThetaPeriodData L) (U : Lˣ) (c : L) :
    thetaFiberAction D U 0 c = c := by
  simp [thetaFiberAction]

/-- The fiber action is multiplicative in the period. -/
theorem thetaFiberAction_add {L : Type u} [NormedField L]
    [IsUltrametricDist L] [CompleteSpace L]
    (D : ThetaPeriodData L) (U : Lˣ) (a b : ℤ) (c : L) :
    thetaFiberAction D U (a + b) c =
      thetaFiberAction D U a (thetaFiberAction D U b c) := by
  unfold thetaFiberAction
  rw [thetaAutomorphyFactor_cocycle D (U : L) (Units.ne_zero U) a b]
  ring

/-- The quotient section over a representative transforms by the actual fiber
action. -/
theorem thetaQuotientSection_fiber_action
    {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
    (D : ThetaPeriodData L) (a : ℤ) (U : Lˣ) :
    (thetaQuotientTotalBundle D).section
        (Quot.mk (thetaPeriodSetoid D) ((thetaRootUnit D) ^ a * U)) =
      Quot.mk (thetaTotalSetoid D)
        (((thetaRootUnit D) ^ a * U),
          thetaFiberAction D U a (oddTheta D.q (U : L))) := by
  rw [thetaQuotientSection_transformation]
  apply congrArg (Quot.mk (thetaTotalSetoid D))
  apply Prod.ext
  · rfl
  · rfl

/-- A local trivialization datum of the quotient total bundle over a period base
point, with the actual fiber equivalence and actual fiber action. -/
structure ThetaQuotientLocalTrivialization
    {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
    (D : ThetaPeriodData L) (b : thetaPeriodBase D) where
  fiberEquiv : thetaQuotientFiber D b ≃ L
  fiberAction : ℤ → thetaQuotientFiber D b → thetaQuotientFiber D b
  action_zero : ∀ c, fiberAction 0 c = c
  action_add : ∀ a b c, fiberAction (a + b) c =
    fiberAction a (fiberAction b c)

/-- Actual local trivialization datum over every period base point. -/
noncomputable def thetaQuotientLocalTrivialization
    {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
    (D : ThetaPeriodData L) (b : thetaPeriodBase D) :
    ThetaQuotientLocalTrivialization D b where
  fiberEquiv := thetaQuotientFiberTrivialization D b
  fiberAction := fun a c => thetaFiberAction D (Quot.out b) a c
  action_zero := by
    intro c
    exact thetaFiberAction_zero D (Quot.out b) c
  action_add := by
    intro a b c
    exact thetaFiberAction_add D (Quot.out b) a b c

end ABCBridge.ThetaQuotientFiberActual

end
