import tmp.sheaf.xif.paper.Node09TateContractionActual
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.AlgebraicClosure

noncomputable section
open LeanFormal.IUT

namespace LeanFormal.IUT.XiFPaper.Node09TateContractionInstanceActual

variable {K : Type*} [Field K]

/-- Actual square root of 4x+1 in the algebraic closure (the extension field). -/
theorem exists_sqrt_algClosure (x : K) :
    ∃ s : AlgebraicClosure K, s ^ 2 = algebraMap K (AlgebraicClosure K) (4 * x + 1) :=
  IsAlgClosed.exists_pow_nat_eq (algebraMap K (AlgebraicClosure K) (4 * x + 1))
    (by norm_num : 0 < 2)

/-- Exact status of the contraction instance over the quadratic extension. -/
def Node09TateContractionInstanceStatus : List String :=
  [ "actual: exists_sqrt_algClosure constructs an actual square root of 4x+1 in the algebraic closure",
    "BLOCKER: Node09TateContractionActual.contractionDataOfSqrt requires a NormedField K; AlgebraicClosure K has no NormedField instance in Mathlib, and no normed quadratic-extension donor exists in the tree",
    "BLOCKER: lifting principal X to full X cannot use the principal root as a singleton fixed point: full X(root) = x + tail(root), generally != x; a full root of X(u)=x (Hensel/coverage) is needed, not the principal root",
    "tail Lipschitz (Node09TateNegativeTailLipschitzActual.xRemainder_lipschitz) is available for a contraction/Newton correction, but not a fixed point at the principal root",
    "no fake, no True/PUnit/axiom/sorry; no NormedField instance is fabricated" ]

end LeanFormal.IUT.XiFPaper.Node09TateContractionInstanceActual