import tmp.sheaf.xif.paper.Mzk1DiagonalIndexActual

/-! GAP-step: explicit 2x2 diagonal quotient cardinal. -/
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1Diag2x2Actual
open LeanFormal.IUT.XiFPaper.Mzk1DiagonalIndexActual
variable {p : Nat} [Fact p.Prime]
theorem natCard_diag2 (e0 e1 : Nat) :
    Nat.card ((Fin 2 → PadicInt p) ⧸
      diagLatticeSubmodule (p := p) (d := Fin 2) (fun i => if i = 0 then e0 else e1)) =
      p ^ e0 * p ^ e1 := by
  rw [natCard_quotient_diagLatticeSubmodule, Fin.prod_univ_two]
  change p ^ (if (0 : Fin 2) = 0 then e0 else e1) *
      p ^ (if (1 : Fin 2) = 0 then e0 else e1) = p ^ e0 * p ^ e1
  rw [if_pos rfl, if_neg (by decide)]
end LeanFormal.IUT.XiFPaper.Mzk1Diag2x2Actual
end