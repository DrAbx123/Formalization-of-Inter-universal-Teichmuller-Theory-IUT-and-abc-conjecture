import tmp.sheaf.xif.paper.S2180BasisCompatiblePairActual
import tmp.sheaf.xif.paper.S2172AffineBasisLiftActual
import Mathlib.Data.Fintype.Card

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2186PairBijectiveActual

open LeanFormal.IUT.XiFPaper.S2180BasisCompatiblePairActual
open LeanFormal.IUT.XiFPaper.S2172AffineBasisLiftActual
open LeanFormal.IUT.XiFPaper.S2166AffinePairCorrespondenceActual
open LeanFormal.IUT.XiFPaper.S2056Psi5RootsActual
open LeanFormal.IUT.XiFPaper.S2009DicksonActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S1906RankTwoTorsionActual

lemma S2186_mem_iff
    (e : (Fin 2 → ZMod S1982Five.value) ≃+ S2056Torsion)
    (x : S2009Pairs) (Q : S2056NonzeroTorsion) :
    Q ∈ (S2180PairMap e x).1 ↔
      ((Q : S2056Torsion) = e x.1 ∨ (Q : S2056Torsion) = -e x.1) := by
  classical
  simp only [S2180PairMap, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h)
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  · rintro (h | h)
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)

theorem S2186PairInv_pairMap
    (e : (Fin 2 → ZMod S1982Five.value) ≃+ S2056Torsion)
    (x : S2009Pairs) :
    S2180PairInv e (S2180PairMap e x) = x := by
  classical
  unfold S2180PairInv
  set P : S2056NonzeroTorsion := Classical.choose
    (Finset.card_pos.mp (by rw [(S2180PairMap e x).2.1]; norm_num)) with hPdef
  have hPmem : P ∈ (S2180PairMap e x).1 := Classical.choose_spec
    (Finset.card_pos.mp (by rw [(S2180PairMap e x).2.1]; norm_num))
  apply Subtype.ext
  change normalize (e.symm (P : S2056Torsion)) = x.1
  have hcases := (S2186_mem_iff e x P).mp hPmem
  rcases hcases with h | h
  · have hv : e.symm (P : S2056Torsion) = x.1 := by
      rw [h, e.symm_apply_apply]
    rw [hv, normalize_of_isRep x.1 x.2]
  · have hv : e.symm (P : S2056Torsion) = -x.1 := by
      rw [h, map_neg, e.symm_apply_apply]
      rfl
    rw [hv, normalize_neg, normalize_of_isRep x.1 x.2]

theorem S2186PairMap_injective
    (e : (Fin 2 → ZMod S1982Five.value) ≃+ S2056Torsion) :
    Function.Injective (S2180PairMap e) := by
  intro x y h
  have h' := congrArg (S2180PairInv e) h
  simpa [S2186PairInv_pairMap e] using h'

/-- The explicit map is bijective: injective from the left inverse, and
surjective from finite cardinality 12 on both sides. -/
theorem S2186PairMap_bijective
    (e : (Fin 2 → ZMod S1982Five.value) ≃+ S2056Torsion) :
    Function.Bijective (S2180PairMap e) := by
  have hcard1 : Fintype.card S2009Pairs = 12 := card_pairRep
  have hcard2 : Fintype.card S2056Pair = 12 := by
    rw [← Nat.card_eq_fintype_card, S2056Pair_card]
  let e0 : S2009Pairs ≃ S2056Pair := Fintype.equivOfCardEq (hcard1.trans hcard2.symm)
  exact ⟨S2186PairMap_injective e,
    Function.Injective.surjective_of_finite e0 (S2186PairMap_injective e)⟩

/-- The actual basis-compatible pair equivalence. -/
noncomputable def S2186BasisCompatiblePairEquiv
    (e : (Fin 2 → ZMod S1982Five.value) ≃+ S2056Torsion) :
    S2180BasisCompatiblePairEquiv e where
  pairEquiv := Equiv.ofBijective (S2180PairMap e) (S2186PairMap_bijective e)
  pairEquiv_apply := fun x => rfl

/-- S2166/S2180 exact target is actual. -/
theorem S2186BasisCompatiblePairEquivRequired_actual :
    S2180BasisCompatiblePairEquivRequired :=
  ⟨S2186BasisCompatiblePairEquiv S2172AffineBasis⟩

end LeanFormal.IUT.XiFPaper.S2186PairBijectiveActual

end
