import tmp.sheaf.xif.paper.S2568FreshmanActual
import tmp.sheaf.xif.paper.S2564Chain1IdentityActual
import tmp.sheaf.xif.paper.S2554Mod613ChainDataActual

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2569GdivActual

open LeanFormal.IUT.XiFPaper.S2554Mod613ChainDataActual
open LeanFormal.IUT.XiFPaper.S2568FreshmanActual

instance : Fact (Nat.Prime 613) := ⟨by norm_num⟩

theorem G_dvd_pow_sub_comp (P : (ZMod 613)[X]) :
    G ∣ P ^ 613 - P.comp T1 := by
  let A := AdjoinRoot G
  let x : A := AdjoinRoot.root G
  have hG0 : G ≠ 0 := by
    intro h
    have : G.natDegree = 0 := by rw [h, natDegree_zero]
    have h12 : G.natDegree = 12 := by unfold G; compute_degree!
    omega
  have hGdeg : G.natDegree = 12 := by unfold G; compute_degree!
  haveI : Nontrivial A := AdjoinRoot.nontrivial (f := G) (by
    rw [Polynomial.degree_eq_natDegree hG0, hGdeg]
    norm_num)
  haveI : CharP A 613 :=
    CharP.of_ringHom_of_ne_zero (algebraMap (ZMod 613) A) 613 (by norm_num)
  have hroot : aeval x T1 = x ^ 613 := by
    have h : aeval x ((X : (ZMod 613)[X]) ^ 613 - T1) = 0 := by
      rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero]
      exact LeanFormal.IUT.XiFPaper.S2564Chain1IdentityActual.chain1_dvd
    rw [map_sub, map_pow, aeval_X, sub_eq_zero] at h
    exact h.symm
  rw [← AdjoinRoot.mk_eq_zero, ← AdjoinRoot.aeval_eq]
  calc aeval x (P ^ 613 - P.comp T1)
      = (aeval x P) ^ 613 - aeval x (P.comp T1) := by rw [map_sub, map_pow]
    _ = (aeval x P) ^ 613 - aeval (aeval x T1) P := by rw [aeval_comp]
    _ = (aeval x P) ^ 613 - aeval (x ^ 613) P := by rw [hroot]
    _ = 0 := by rw [aeval_pow_613, sub_self]

#print axioms G_dvd_pow_sub_comp

end LeanFormal.IUT.XiFPaper.S2569GdivActual
end