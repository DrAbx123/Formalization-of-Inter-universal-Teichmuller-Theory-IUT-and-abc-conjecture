import tmp.sheaf.xif.paper.Mzk1P5LabelShiftActual

/-!
# CONDITIONAL (named inputs): P5-A analytic/root theta comparison

This file does NOT construct the analytic-to-root bridge.  It isolates the
missing bridge into two named inputs and proves the conditional comparison:

1. AnalyticRootMap: a ring map from the analytic normed field L to a root
   field R, together with a distinguished analytic root r and its image qRoot;
2. ThetaValueComparison: a constant c and the comparison of the analytic
   normalized power r^(-(j^2)) with the root power qRoot^(j^2).

Under these inputs the conditional theorem rewrites the actual analytic
normalized theta ratio to c * qRoot^(j^2), with the exponent j^2 aligned and
c explicit.  The two inputs are named data, not constructed objects.  This is
not a construction of paperRootThetaUnit, a line-bundle section, or a Kummer
class; see coord/ROUTE3-CTHETA.md.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1P5CompareActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.Mzk1P5LabelShiftActual
open LeanFormal.IUT.Foundations.Theta

variable {L R : Type*} [Field L] [Field R]

/-- Named input 1: the analytic root r, a target root qRoot, and a ring map
L -> R carrying r to qRoot.  No existence or construction of such a map is
asserted. -/
structure AnalyticRootMap (l : PrimeGeFive) where
  toRoot : L →+* R
  r : L
  qRoot : R
  root_image : toRoot r = qRoot ^ l.value

/-- Named input 2: the comparison of the analytic normalized power
r^(-(j^2)) with the root power qRoot^(j^2), up to a constant c. -/
structure ThetaValueComparison (l : PrimeGeFive)
    (M : AnalyticRootMap (L := L) (R := R) l) where
  c : R
  comparison : ∀ j : ThetaLabel (l := l),
    M.toRoot (M.r ^ (-(thetaLabelExponent (l := l) j ^ 2))) =
      c * M.qRoot ^ (thetaLabelExponent (l := l) j ^ 2)

variable {L' : Type*} [NormedField L'] [IsUltrametricDist L'] [CompleteSpace L']

/-- Conditional P5-A comparison theorem: the actual analytic normalized theta
ratio is c times qRoot^(j^2), with no construction of the named inputs. -/
theorem p5_compare_conditional
    (M : AnalyticRootMap (L := L') (R := R) l)
    (T : ThetaValueComparison (L := L') (R := R) (l := l) M)
    (q i : L') (hr : M.r ^ 2 = q) (hr0 : M.r ≠ 0) (hi : i ^ 2 = -1)
    (hq : ‖q‖ < 1) (hTheta : oddTheta q i ≠ 0)
    (j : ThetaLabel (l := l)) :
    M.toRoot (oddTheta q (analyticThetaLabelPoint i M.r j) / oddTheta q i) =
      T.c * M.qRoot ^ (thetaLabelExponent (l := l) j ^ 2) := by
  rw [oddThetaFraction_eval_thetaLabel q M.r i hr hr0 hi hq hTheta j]
  exact T.comparison j

#print axioms p5_compare_conditional

end LeanFormal.IUT.XiFPaper.Mzk1P5CompareActual
