import tmp.sheaf.xif.paper.S2057DedekindFrobBridgeActual
import tmp.sheaf.xif.paper.S2056Psi5RootsPairsActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
open Polynomial
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S2056Psi5RootsPairsActual

namespace Prob2132b

abbrev L := S2057FiveDivisionField
instance : DecidableEq L := Classical.decEq _
abbrev R := S2057Psi5F.rootSet L
example : Fintype R := inferInstance
instance : DecidableEq R := Classical.decEq _

theorem hsplit : (S2057Psi5F.map (algebraMap S1720Field L)).Splits :=
  Polynomial.SplittingField.splits

theorem R_card : Fintype.card R = 12 := by
  have h := Polynomial.card_rootSet_eq_natDegree (p := S2057Psi5F) (K := L)
    S2057Psi5F_separable hsplit
  have hdeg : S2057Psi5F.natDegree = 12 := by
    rw [S2057Psi5F, Polynomial.natDegree_map]
    simpa [S2057Psi5Q, S2056Psi5] using S2056Psi5_natDegree
  rw [h, hdeg]

noncomputable def rmap (σ : L ≃ₐ[S1720Field] L) (x : R) : R :=
  ⟨σ x.1, Polynomial.rootSet_mapsTo (p := S2057Psi5F) σ.toAlgHom x.2⟩

noncomputable def requiv (σ : L ≃ₐ[S1720Field] L) : R ≃ R where
  toFun := rmap σ
  invFun := rmap σ.symm
  left_inv x := by apply Subtype.ext; exact σ.symm_apply_apply x.1
  right_inv x := by apply Subtype.ext; exact σ.apply_symm_apply x.1

def honest : Prop :=
  ∃ σ : L ≃ₐ[S1720Field] L, (requiv σ).cycleType = ({2, 10} : Multiset Nat)

example : L ≃ₐ[S1720Field] L := AlgEquiv.refl

end Prob2132b
