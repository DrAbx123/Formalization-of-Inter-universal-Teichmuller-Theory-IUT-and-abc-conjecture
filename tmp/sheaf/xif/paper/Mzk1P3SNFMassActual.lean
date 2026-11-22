import tmp.sheaf.xif.paper.Mzk1SNFMatrixDiagActual
import Mathlib.NumberTheory.Padics.PadicIntegers
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P3SNFMassActual
open scoped BigOperators
/-- SNF diagonal mass ratio as the product of prime powers of the valuations. -/
noncomputable def snfMassRatio {p : Nat} [Fact p.Prime] {ι : Type*} [Fintype ι]
    (a : ι → PadicInt p) : Nat :=
  ∏ i, p ^ (a i).valuation
theorem snfMassRatio_pos {p : Nat} [Fact p.Prime] {ι : Type*} [Fintype ι]
    (a : ι → PadicInt p) : 0 < snfMassRatio a := by
  unfold snfMassRatio
  exact Finset.prod_pos (fun i _ => pow_pos (Fact.out : Nat.Prime p).pos _)
end LeanFormal.IUT.XiFPaper.Mzk1P3SNFMassActual
end