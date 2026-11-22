import tmp.sheaf.xif.paper.S2180BasisCompatiblePairActual
open LeanFormal.IUT.XiFPaper.S2180BasisCompatiblePairActual
open LeanFormal.IUT.XiFPaper.S2056Psi5RootsActual
open LeanFormal.IUT.XiFPaper.S2009DicksonActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S1906RankTwoTorsionActual
noncomputable section
set_option maxHeartbeats 4000000
namespace Probe2186
lemma mem_iff (e : (Fin 2 → ZMod S1982Five.value) ≃+ S2056Torsion) (x : S2009Pairs) (Q : S2056NonzeroTorsion) :
    Q ∈ (S2180PairMap e x).1 ↔ ((Q : S2056Torsion) = e x.1 ∨ (Q : S2056Torsion) = -e x.1) := by
  classical
  simp only [S2180PairMap, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h)
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  · rintro (h | h)
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
example (e : (Fin 2 → ZMod S1982Five.value) ≃+ S2056Torsion) (x : S2009Pairs) :
    S2180PairInv e (S2180PairMap e x) = x := by
  classical
  unfold S2180PairInv
  set P : S2056NonzeroTorsion := Classical.choose (Finset.card_pos.mp (by rw [(S2180PairMap e x).2.1]; norm_num)) with hPdef
  have hPmem : P ∈ (S2180PairMap e x).1 := Classical.choose_spec (Finset.card_pos.mp (by rw [(S2180PairMap e x).2.1]; norm_num))
  apply Subtype.ext
  change normalize (e.symm (P : S2056Torsion)) = x.1
  have hcases := (mem_iff e x P).mp hPmem
  rcases hcases with h | h
  · have hv : e.symm (P : S2056Torsion) = x.1 := by
      rw [h, e.symm_apply_apply]
    rw [hv, normalize_of_isRep x.1 x.2]
  · have hv : e.symm (P : S2056Torsion) = -x.1 := by
      rw [h, map_neg, e.symm_apply_apply]
      rfl
    rw [hv, normalize_neg, normalize_of_isRep x.1 x.2]
end Probe2186
end
