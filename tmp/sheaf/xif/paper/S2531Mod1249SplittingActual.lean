import tmp.sheaf.xif.paper.S2481PairTransitiveHardActual
import tmp.sheaf.xif.paper.S2531Mod1249CertificateActual

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
open Polynomial

local instance : Fact (Nat.Prime 1249) := ⟨by norm_num⟩

namespace LeanFormal.IUT.XiFPaper.S2531Mod1249SplittingActual

open LeanFormal.IUT.XiFPaper.S2481PairTransitiveHardActual

abbrev S2481H1249 : (ZMod 1249)[X] :=
  C 1080 + C 4 * X ^ 2 + C 980 * X ^ 4 + C 1055 * X ^ 6 + C 248 * X ^ 8

lemma S2481HZ_mod1249 :
    LeanFormal.IUT.XiFPaper.S2481PairTransitiveHardActual.S2481HZ.map (Int.castRingHom (ZMod 1249)) = S2481H1249 := by
  ext n
  by_cases hn : n ≤ 8
  · interval_cases n <;>
      (simp [LeanFormal.IUT.XiFPaper.S2481PairTransitiveHardActual.S2481HZ, S2481H1249,
        Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_X_pow,
        Polynomial.coeff_X, Polynomial.coeff_one] <;> norm_num)
  · have h1 : (LeanFormal.IUT.XiFPaper.S2481PairTransitiveHardActual.S2481HZ.map (Int.castRingHom (ZMod 1249))).coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have hle : (LeanFormal.IUT.XiFPaper.S2481PairTransitiveHardActual.S2481HZ.map (Int.castRingHom (ZMod 1249))).natDegree ≤
          LeanFormal.IUT.XiFPaper.S2481PairTransitiveHardActual.S2481HZ.natDegree := Polynomial.natDegree_map_le
      have h8 : LeanFormal.IUT.XiFPaper.S2481PairTransitiveHardActual.S2481HZ.natDegree = 8 := by
        unfold LeanFormal.IUT.XiFPaper.S2481PairTransitiveHardActual.S2481HZ; compute_degree!
      omega
    have h2 : S2481H1249.coeff n = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      have h8 : S2481H1249.natDegree = 8 := by unfold S2481H1249; compute_degree!
      omega
    rw [h1, h2]

lemma S2481H1249_natDegree : S2481H1249.natDegree = 8 := by
  unfold S2481H1249; compute_degree!

lemma S2481H1249_ne_zero : S2481H1249 ≠ 0 := by
  intro h; have hd := S2481H1249_natDegree; rw [h] at hd; simp at hd

lemma S2481H1249_roots :
    ∀ r : ZMod 1249, r ∈ ({32, 118, 300, 585, 664, 949, 1131, 1217} : Finset (ZMod 1249)) →
      S2481H1249.IsRoot r := by
  intro r hr
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp [Polynomial.IsRoot, S2481H1249] <;> norm_num)

lemma S2481H1249_roots_card : S2481H1249.roots.card = 8 := by
  have hcard : ({32, 118, 300, 585, 664, 949, 1131, 1217} : Finset (ZMod 1249)).card = 8 := by decide
  have hsub : ({32, 118, 300, 585, 664, 949, 1131, 1217} : Finset (ZMod 1249)) ⊆ S2481H1249.roots.toFinset := by
    intro r hr
    rw [Multiset.mem_toFinset, Polynomial.mem_roots S2481H1249_ne_zero]
    exact S2481H1249_roots r hr
  have h1 : 8 ≤ S2481H1249.roots.toFinset.card := by rw [← hcard]; exact Finset.card_le_card hsub
  have h2 : S2481H1249.roots.toFinset.card ≤ S2481H1249.roots.card := Multiset.toFinset_card_le _
  have h3 : S2481H1249.roots.card ≤ S2481H1249.natDegree := Polynomial.card_roots' _
  rw [S2481H1249_natDegree] at h3
  omega

theorem S2531Mod1249ResidueDegreeOne_actual :
    (LeanFormal.IUT.XiFPaper.S2481PairTransitiveHardActual.S2481HZ.map (Int.castRingHom (ZMod 1249))).Splits := by
  rw [S2481HZ_mod1249, Polynomial.splits_iff_card_roots, S2481H1249_roots_card, S2481H1249_natDegree]

#print axioms S2531Mod1249ResidueDegreeOne_actual

end LeanFormal.IUT.XiFPaper.S2531Mod1249SplittingActual
end
