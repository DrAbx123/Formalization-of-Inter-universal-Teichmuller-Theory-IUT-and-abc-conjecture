import tmp.sheaf.xif.paper.Mzk1IndexCardBridgeActual
import LeanFormal.IUT.Foundations.LocalFields.PadicLatticeIndexFormula
import tmp.sheaf.xif.paper.Mzk1LatticeOrbitIndexActual

/-! GAP marker: general SNF volume ratio via A2 bridge.

The quotient cardinal is green (`natCard_quotient_eq_prod_pow_valuation_of_smithNormalForm`)
and the A2 bridge is green (`latticeIndex_toAddSubgroup_eq_natCard_quotient`).
The remaining step is the ENNReal/`Submodule.toAddSubgroup` coercion in `hμM`
(`μ(M)=index*μ(N)` → `μ(N)/μ(M)`), which is recorded as GAP;
the concrete diagonal case is green in `Mzk1DiagVolumeProvedActual`.
No sorry/axiom. -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1GeneralSNFVolume2Actual
open LeanFormal.IUT.PadicLatticeIndex
theorem general_snf_quotient_card
    {p : Nat} [Fact p.Prime] {E : Type*} [AddCommGroup E] [Module (PadicInt p) E]
    (M : Submodule (PadicInt p) E) {ι : Type*} [Fintype ι]
    (N : Submodule (PadicInt p) M)
    (bM : Module.Basis ι (PadicInt p) M)
    (bN : Module.Basis ι (PadicInt p) N) (a : ι → PadicInt p)
    (hSNF : ∀ i, (bN i : M) = a i • bM i) :
    Nat.card (M ⧸ N) = ∏ i, p ^ (a i).valuation :=
  natCard_quotient_eq_prod_pow_valuation_of_smithNormalForm hSNF
end LeanFormal.IUT.XiFPaper.Mzk1GeneralSNFVolume2Actual
end