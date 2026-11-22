import tmp.sheaf.xif.paper.S2056Psi5RootsActual
import tmp.sheaf.xif.paper.S2009DicksonActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
open Polynomial
open LeanFormal.IUT.XiFPaper.S2056Psi5RootsActual
open LeanFormal.IUT.XiFPaper.S2009DicksonActual

namespace Prob2132

example : Fintype S2056Pair := inferInstance

theorem disjoint_permCongr {α β : Type*} {e : α ≃ β} {f g : Equiv.Perm α}
    (h : Equiv.Perm.Disjoint f g) :
    Equiv.Perm.Disjoint (e.permCongr f) (e.permCongr g) := by
  rw [Equiv.Perm.disjoint_iff_eq_or_eq] at h ⊢
  intro y
  rcases h (e.symm y) with hf | hg
  · left; simp [Equiv.permCongr_apply, hf]
  · right; simp [Equiv.permCongr_apply, hg]

theorem cycleType_permCongr {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (σ : Equiv.Perm α) : (e.permCongr σ).cycleType = σ.cycleType := by
  induction σ using Equiv.Perm.cycle_induction_on with
  | base_one => simpa using map_one (Equiv.permCongrHom e)
  | base_cycles σ hσ =>
      rw [(isCycle_permCongr (e := e) hσ).cycleType, hσ.cycleType, card_support_permCongr e σ]
  | induction_disjoint σ τ hd hc hσ hτ =>
      rw [Equiv.permCongr_mul, hd.cycleType_mul,
        (disjoint_permCongr (e := e) hd).cycleType_mul, hσ, hτ]

theorem pair_card_fintype : Fintype.card S2056Pair = 12 := by
  rw [← Nat.card_eq_fintype_card, S2056Pair_card]

noncomputable def e2009 : S2009Pairs ≃ S2056Pair :=
  Fintype.equivOfCardEq (by
    rw [card_pairRep, pair_card_fintype])

theorem pairCycle_exists :
    ∃ ρ : Equiv.Perm S2056Pair, ρ.cycleType = ({2, 10} : Multiset Nat) := by
  classical
  refine ⟨e2009.permCongr C, ?_⟩
  rw [cycleType_permCongr, cycleType_C]
  decide

end Prob2132
