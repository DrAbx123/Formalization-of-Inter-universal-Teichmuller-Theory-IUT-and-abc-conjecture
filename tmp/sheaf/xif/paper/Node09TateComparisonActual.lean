import tmp.sheaf.xif.paper.Node09TateFixedPointActual
import LeanFormal.IUT.Foundations.PAdicAnalytic.TateJGeneral
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.AlgebraicClosure

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.PAdicAnalytic

namespace LeanFormal.IUT.XiFPaper.Node09TateComparisonActual

local instance fivePrimeFactTateComp : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- Actual Tate q with H(q)=t, j(q)=t^{-1}, |q|<1 and |q|=|t| in Q_5. -/
theorem exists_actualTateQ_comparison
    (hint : ∀ n : ℕ, ‖(n : ℚ_[5])‖ ≤ 1)
    (h1728 : ‖(1728 : ℚ_[5])‖ = 1)
    {t : ℚ_[5]} (ht0 : t ≠ 0) (ht1 : ‖t‖ < 1) :
    ∃ q : ℚ_[5], tateHK q = t ∧ tateJK q = t⁻¹ ∧
      ‖q‖ < 1 ∧ ‖q‖ = ‖t‖ :=
  Node09TateFixedPointActual.exists_actualTateQ_norm_eq hint h1728 ht0 ht1

/-- Tate comparison with an actual elliptic curve E whose j-invariant is t^{-1}. -/
theorem tateComparison_of_j_eq
    (hint : ∀ n : ℕ, ‖(n : ℚ_[5])‖ ≤ 1)
    (h1728 : ‖(1728 : ℚ_[5])‖ = 1)
    {t : ℚ_[5]} (ht0 : t ≠ 0) (ht1 : ‖t‖ < 1)
    (E : WeierstrassCurve ℚ_[5]) (hE : E.IsElliptic)
    (hj : @WeierstrassCurve.j ℚ_[5] _ E hE = t⁻¹) :
    ∃ q : ℚ_[5], @WeierstrassCurve.j ℚ_[5] _ E hE = tateJK q ∧
      tateHK q = t ∧ tateJK q = t⁻¹ ∧ ‖q‖ < 1 ∧ ‖q‖ = ‖t‖ := by
  obtain ⟨q, hqH, hqJ, hq1, hqnorm⟩ :=
    exists_actualTateQ_comparison hint h1728 ht0 ht1
  exact ⟨q, hj.trans hqJ.symm, hqH, hqJ, hq1, hqnorm⟩

/-- Actual (2l)-th root of q in the algebraic closure (root-to-K_v first half). -/
theorem exists_twoL_root_algClosure
    (l : PrimeGeFive) (q : ℚ_[5]) (hq : q ≠ 0) :
    ∃ α : AlgebraicClosure ℚ_[5],
      α ^ (2 * l.value) = algebraMap ℚ_[5] (AlgebraicClosure ℚ_[5]) q := by
  exact IsAlgClosed.exists_pow_nat_eq
    (algebraMap ℚ_[5] (AlgebraicClosure ℚ_[5]) q)
    (by
    have h5 := l.ge_five
    omega : 0 < 2 * l.value)

def Node09TateComparisonStatus : List String :=
  [ "actual: exists_actualTateQ_comparison / tateComparison_of_j_eq give q with H(q)=t, j(q)=t^{-1}, |q|<1, |q|=|t| and comparison to an actual E with j(E)=t^{-1}",
    "actual: exists_twoL_root_algClosure gives alpha^(2*l)=q in the algebraic closure",
    "BLOCKER root-to-K_v: no theorem proves alpha lies in the specified K_v/root field; needs actual 2l-torsion rationality + Galois descent, which is not in the tree",
    "no fake, no True/PUnit/axiom/sorry" ]

end LeanFormal.IUT.XiFPaper.Node09TateComparisonActual