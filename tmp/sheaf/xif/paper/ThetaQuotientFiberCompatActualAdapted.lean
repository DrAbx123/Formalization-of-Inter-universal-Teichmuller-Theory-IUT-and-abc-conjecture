import tmp.sheaf.xif.paper.ThetaQuotientFiberActualAdapted

/-!
# Actual compatibility of the quotient local trivialization

This file proves the compatibility of the constructed quotient local
trivialization with the quotient projection and the section transformation law.
All maps are the actual maps of ThetaQuotientTotalActual/FiberActual; no source
curve comparison is made and no inequality is asserted.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ABCBridge.ThetaQuotientFiberCompatActualAdapted

open LeanFormal.IUT.Foundations.Theta

universe u

/-- Projection of an explicit total representative. -/
theorem thetaQuotientProjection_mk
    {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
    (D : ThetaPeriodData L) (U : Lˣ) (c : L) :
    thetaQuotientProjection D
        (Quot.mk (thetaTotalSetoid D) (U, c)) =
      Quot.mk (thetaPeriodSetoid D) U :=
  rfl

/-- The projection is constant on the actual total relation. -/
theorem thetaQuotientProjection_eq_of_rel
    {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
    (D : ThetaPeriodData L) {x y : Lˣ × L}
    (h : thetaTotalRel D x y) :
    thetaQuotientProjection D (Quot.mk (thetaTotalSetoid D) x) =
      thetaQuotientProjection D (Quot.mk (thetaTotalSetoid D) y) := by
  rcases h with ⟨a, hV, _hd⟩
  change Quot.mk (thetaPeriodSetoid D) x.1 =
    Quot.mk (thetaPeriodSetoid D) y.1
  apply Quot.sound
  exact ⟨a, hV⟩

/-- The quotient section projects to its base point. -/
theorem thetaQuotientSection_projection
    {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
    (D : ThetaPeriodData L) (U : Lˣ) :
    thetaQuotientProjection D
        ((thetaQuotientTotalBundle D).section
          (Quot.mk (thetaPeriodSetoid D) U)) =
      Quot.mk (thetaPeriodSetoid D) U := by
  rw [thetaQuotientSection_mk]
  rfl

/-- The local fiber action is exactly the actual automorphy-factor action at the
chosen representative. -/
theorem thetaQuotientLocalTrivialization_fiberAction_eq
    {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
    (D : ThetaPeriodData L) (b : thetaPeriodBase D) (a : ℤ) (c : L) :
    (thetaQuotientLocalTrivialization D b).fiberAction a c =
      thetaFiberAction D (Quot.out b) a c :=
  rfl

/-- The local fiber action satisfies the actual additive law. -/
theorem thetaQuotientLocalTrivialization_fiberAction_add
    {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
    (D : ThetaPeriodData L) (b : thetaPeriodBase D) (a a' : ℤ) (c : L) :
    (thetaQuotientLocalTrivialization D b).fiberAction (a + a') c =
      (thetaQuotientLocalTrivialization D b).fiberAction a
        ((thetaQuotientLocalTrivialization D b).fiberAction a' c) :=
  (thetaQuotientLocalTrivialization D b).action_add a a' c

/-- The section transformation law is compatible with the actual local fiber
action at the representative chosen by Quot.out of the base point. -/
theorem thetaQuotientSection_local_fiber_action
    {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
    (D : ThetaPeriodData L) (a : ℤ) (U : Lˣ) :
    (thetaQuotientTotalBundle D).section
        (Quot.mk (thetaPeriodSetoid D)
          ((thetaRootUnit D) ^ a * U)) =
      Quot.mk (thetaTotalSetoid D)
        (((thetaRootUnit D) ^ a * U),
          thetaFiberAction D U a (oddTheta D.q (U : L))) :=
  thetaQuotientSection_fiber_action D a U

end ABCBridge.ThetaQuotientFiberCompatActualAdapted

end
