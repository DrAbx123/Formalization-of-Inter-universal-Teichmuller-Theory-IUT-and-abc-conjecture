/- R3a (5/n): the base block K0 = ℚ(λ, √(-1)) and integrality of the Ψ₃-root set over it.

  SOURCE INPUT (Lead ruling): `hlam : IsAlgebraic ℚ lam` — IUT's λ is a fixed algebraic
  parameter; without it ℚ(λ) is not a number field and no degree bound exists. Documented here
  as a source input, not an obligation.

  SEMANTIC LAYER (Lead ruling): the elements of `threeTorsionX` are roots of the division
  polynomial ψ₃ = legendreΨ₃; they are NOT asserted to be actual E[3]-torsion coordinates here
  (for n = 3 that identification is available via S1373ZeroCriterionActual; for n = 5/l it needs
  the multiplication-kernel route and is NOT claimed).

  RECON: `IntermediateField.finiteDimensional_adjoin` (Adjoin/Basic.lean:578);
  `IsAlgebraic.isIntegral` (Algebraic/Integral.lean:79); `legendreΨ₃` + `legendreΨ₃_eval`
  (Mzk1G1F2ThetaDivisionPolynomialsActual). No sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1G1F2ThetaCompositumActual
import tmp.sheaf.xif.paper.Mzk1G1F2ThetaDivisionPolynomialsActual
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Tactic

noncomputable section
open Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1F2ThetaCompositumDegreeActual
open LeanFormal.IUT.XiFPaper.Mzk1G1F2ThetaCompositumActual
open LeanFormal.IUT.XiFPaper.Mzk1G1F2ThetaDivisionPolynomialsActual

variable (lam : ℂ)

/-- 基础块 `K0 = ℚ(λ, √(-1))`。 -/
noncomputable def BaseBlock (lam : ℂ) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ ({lam, Complex.I} : Set ℂ)

theorem lam_mem_BaseBlock : lam ∈ BaseBlock lam := by
  exact IntermediateField.subset_adjoin ℚ _ (by simp)

theorem I_mem_BaseBlock : Complex.I ∈ BaseBlock lam := by
  exact IntermediateField.subset_adjoin ℚ _ (by simp)

/-- `√(-1)` 在 ℚ 上代数（`X²+1`）。 -/
theorem isAlgebraic_I : IsAlgebraic ℚ Complex.I :=
  ⟨X ^ 2 + 1, by
    intro h
    have hc := congrArg (fun p : Polynomial ℚ => p.coeff 0) h
    simp at hc, by
    simp [Complex.I_sq]⟩

/-- `√(-1)` 在 ℚ 上整。 -/
theorem isIntegral_I : IsIntegral ℚ Complex.I :=
  isAlgebraic_I.isIntegral

/-- **源输入**：`lam` 在 ℚ 上代数 ⇒ 整。 -/
theorem isIntegral_lam (hlam : IsAlgebraic ℚ lam) : IsIntegral ℚ lam :=
  hlam.isIntegral


/-- 一般引理：若 `g : K0[X]` monic 且 `x` 是 `g` 在 ℂ 中的根（经 `map`），则 `x` 在 `K0` 上整。 -/
theorem isIntegral_of_monic_map_eval {K0 : Type*} [Field K0] [Algebra K0 ℂ]
    (g : Polynomial K0) (hg : g.Monic) {x : ℂ}
    (hx : (g.map (algebraMap K0 ℂ)).eval x = 0) : IsIntegral K0 x := by
  refine ⟨g, hg, ?_⟩
  rwa [Polynomial.eval₂_eq_eval_map]

#print axioms lam_mem_BaseBlock
#print axioms I_mem_BaseBlock
#print axioms isAlgebraic_I
#print axioms isIntegral_I
#print axioms isIntegral_lam
#print axioms isIntegral_of_monic_map_eval

end LeanFormal.IUT.XiFPaper.Mzk1G1F2ThetaCompositumDegreeActual