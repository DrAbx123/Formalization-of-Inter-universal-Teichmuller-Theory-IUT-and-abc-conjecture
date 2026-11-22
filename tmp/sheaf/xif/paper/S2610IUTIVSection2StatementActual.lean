import Mathlib

/-!
# IUT IV §2 / Theorem A estimate statement (Lean statement schema)

Paper anchor: IUT IV Theorem A / Corollary 2.3, corpus lines IV:93-105;
as quoted in
`LeanFormal/IUT/ABCBridge/Arithmetic/ABCHeightArithmeticWeightComparison.lean:143-145`:

  ht_{omegaX(D)} <~ (1 + eps) * (log-diff_X + log-cond_D)
  (bounded discrepancy classes).

The tree has no formal `log-diff` / `log-cond` invariants for a proper smooth
curve over a number field.  This file records the exact statement shape at the
level of the paper's three real-valued invariants, with the bounded-discrepancy
class as explicit data.  It is a statement schema, not a construction of the
paper's curve/line-bundle objects and not a proof of the estimate.
-/

noncomputable section
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2610IUTIVSection2StatementActual

universe u

/-- Data of IUT IV §2: a class of algebraic points, the height of the line
bundle `omegaX(D)`, the log-difference and log-conductor invariants, and the
bounded-discrepancy class condition.

The field `boundedDiscrepancy` is the paper's hypothesis that the class is a
bounded discrepancy class; it is stated as a bound on `|logDiff + logCond|`
on that class. -/
structure IUTIVSection2Data where
  /-- The class of algebraic points. -/
  Point : Type u
  /-- Height of `omegaX(D)` (paper `ht_{omegaX(D)}`). -/
  heightTheta : Point -> Real
  /-- Log-difference invariant (paper `log-diff_X`). -/
  logDiff : Point -> Real
  /-- Log-conductor invariant (paper `log-cond_D`). -/
  logCond : Point -> Real
  /-- The bounded discrepancy class. -/
  discrepancyClass : Set Point
  /-- Bounded discrepancy on the class: `|log-diff + log-cond|` is bounded. -/
  boundedDiscrepancy : exists B : Real,
    forall x : Point, x ∈ discrepancyClass ->
      |logDiff x + logCond x| <= B

/-- The IUT IV §2 / Theorem A estimate, exactly in the paper's shape: for
every `eps > 0` there is a constant `C` such that on the bounded discrepancy
class

  ht_{omegaX(D)} <= (1 + eps) * (log-diff_X + log-cond_D) + C. -/
def IUTIVSection2Estimate (D : IUTIVSection2Data) : Prop :=
  forall eps : Real, 0 < eps -> exists C : Real,
    forall x : D.Point, x ∈ D.discrepancyClass ->
      D.heightTheta x <=
        (1 + eps) * (D.logDiff x + D.logCond x) + C

/-- The estimate is definitionally the paper shape. -/
theorem IUTIVSection2Estimate_iff (D : IUTIVSection2Data.{u}) :
    IUTIVSection2Estimate D <->
      forall eps : Real, 0 < eps -> exists C : Real,
        forall x : D.Point, x ∈ D.discrepancyClass ->
          D.heightTheta x <=
            (1 + eps) * (D.logDiff x + D.logCond x) + C := Iff.rfl

#print axioms IUTIVSection2Estimate_iff

end LeanFormal.IUT.XiFPaper.S2610IUTIVSection2StatementActual
end
