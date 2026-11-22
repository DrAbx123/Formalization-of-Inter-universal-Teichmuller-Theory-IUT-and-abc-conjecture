import tmp.sheaf.xif.paper.Mzk1DiagonalIndexActual

/-! CONDITIONAL wrapper: f-version of the diagonal quotient cardinal. -/
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1DiagCardFActual
open LeanFormal.IUT.XiFPaper.Mzk1DiagonalIndexActual
variable {p : Nat} [Fact p.Prime] {d : Type} [Fintype d] [DecidableEq d]
theorem natCard_diagQuotient_f (f : d → Nat) :
    Nat.card ((d → PadicInt p) ⧸ diagLatticeSubmodule (p := p) (d := d) f) =
      ∏ i, p ^ (f i) :=
  natCard_quotient_diagLatticeSubmodule (p := p) (d := d) f
end LeanFormal.IUT.XiFPaper.Mzk1DiagCardFActual
end