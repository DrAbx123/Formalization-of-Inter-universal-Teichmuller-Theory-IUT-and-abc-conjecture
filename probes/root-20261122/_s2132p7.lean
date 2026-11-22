import tmp.sheaf.xif.paper.S2057DedekindFrobBridgeActual
import tmp.sheaf.xif.paper.S2055DicksonClassActual
import tmp.sheaf.xif.paper.S2056Psi5RootsPairsActual
import tmp.sheaf.xif.paper.S2041D5LargeImageFirstMilestoneActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
open Polynomial
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S2009DicksonActual
open LeanFormal.IUT.XiFPaper.S2055DicksonClassActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S2056Psi5RootsActual
open LeanFormal.IUT.XiFPaper.S2056Psi5RootsPairsActual
open LeanFormal.IUT.XiFPaper.S2041D5LargeImageFirstMilestoneActual

namespace Prob2132f

abbrev L := S2057FiveDivisionField
instance : DecidableEq L := Classical.decEq _
abbrev R := S2057Psi5F.rootSet L
instance : DecidableEq R := Classical.decEq _

theorem hsplit : (S2057Psi5F.map (algebraMap S1720Field L)).Splits :=
  Polynomial.SplittingField.splits (f := S2057Psi5F)

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

theorem honestRoot : Prop :=
  ∃ σ : L ≃ₐ[S1720Field] L, Equiv.Perm.cycleType (requiv σ) = ({2, 10} : Multiset Nat)

theorem pair_card : Fintype.card S2056Pair = 12 := by
  rw [← Nat.card_eq_fintype_card, S2056Pair_card]

noncomputable def rootPairBijection : R ≃ S2056Pair :=
  Fintype.equivOfCardEq (R_card.trans pair_card.symm)

theorem honestPair : Prop :=
  ∃ σ : L ≃ₐ[S1720Field] L,
    Equiv.Perm.cycleType (rootPairBijection.permCongr (requiv σ)) = ({2, 10} : Multiset Nat)

theorem honestRoot_iff_honestPair : honestRoot ↔ honestPair := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨σ, by rw [cycleType_permCongr, hσ]⟩
  · rintro ⟨σ, hσ⟩
    refine ⟨σ, ?_⟩
    have := hσ
    rw [cycleType_permCongr] at this
    exact this

theorem bridge_of_factorization_and_honest
    (fact : S2057Mod29FactorizationData) (h : honestPair) :
    S2057FrobMod29CycleTypeBridge where
  factorization := fact
  frobenius := AlgEquiv.refl
  permutation := rootPairBijection.permCongr (requiv h.choose)
  cycleType_eq := h.choose_spec

theorem pairCycle_exists : ∃ ρ : Equiv.Perm S2056Pair, ρ.cycleType = ({2, 10} : Multiset Nat) := by
  classical
  -- transport S2009 C
  let e : S2009Pairs ≃ S2056Pair := Fintype.equivOfCardEq (by
    rw [card_pairRep, pair_card])
  refine ⟨e.permCongr C, ?_⟩
  rw [cycleType_permCongr, cycleType_C]
  decide

theorem imageTail_of_cycleType_and_transitive (H : Subgroup GL2)
    (h102 : HasCycleType102 H) (htrans : PairTransitive H) :
    Subgroup.map Matrix.SpecialLinearGroup.toGL
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K5)) ≤ H := by
  have h5 : 5 ∣ Nat.card H := by
    obtain ⟨h, hh, hc⟩ := h102
    exact dvd_trans (by norm_num : 5 ∣ 10) (ten_dvd_natCard_of_mem_cycleType102 hh hc)
  have hle := sl_le_of_five_dvd H htrans h5
  rwa [closure_trv_eq_map, closure_sl_eq_top] at hle

theorem d5_of_rangeHypotheses (b : S1725TorsionBasis S1987Five)
    (h102 : HasCycleType102
      (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range)
    (htrans : PairTransitive
      (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range) :
    S1987D5LargeImageFive :=
  (S1987D5LargeImageFive_iff_tail b).mpr
    (imageTail_of_cycleType_and_transitive _ h102 htrans)

end Prob2132f
