import LeanFormal.IUT.Foundations.LocalFields.PadicLatticeIndexFormula

/-! CONDITIONAL/GAP: general SNF quotient cardinal (volume link remains GAP).

Reuses `PaddingLatticeIndexFormula.natCard_quotient_eq_prod_pow_valuation_of_smithNormalForm`:
for a full-rank SNF witness `(bN i : M) = a i • bM i`,
`Nat.card (M ⧸ N) = ∏ p^{v_p(a i)}`.  The Haar volume bridge
`μ(N)/μ(M) = ∏|a i|_p` needs the A2 interface and is recorded as GAP
(the concrete diagonal case is green in `Mzk1DiagVolumeProvedActual`).
No sorry/axiom. -/
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1GeneralSNFVolumeActual
open LeanFormal.IUT.PadicLatticeIndex
open Module

variable {p : Nat} [Fact p.Prime] {E : Type*} [AddCommGroup E] [Module (PadicInt p) E]
variable (M : Submodule (PadicInt p) E) {ι : Type*} [Fintype ι]

theorem general_snf_quotient_card
    (N : Submodule (PadicInt p) M)
    (bM : Module.Basis ι (PadicInt p) M)
    (bN : Module.Basis ι (PadicInt p) N) (a : ι → PadicInt p)
    (hSNF : ∀ i, (bN i : M) = a i • bM i) :
    Nat.card (M ⧸ N) = ∏ i, p ^ (a i).valuation :=
  natCard_quotient_eq_prod_pow_valuation_of_smithNormalForm hSNF

end LeanFormal.IUT.XiFPaper.Mzk1GeneralSNFVolumeActual
end