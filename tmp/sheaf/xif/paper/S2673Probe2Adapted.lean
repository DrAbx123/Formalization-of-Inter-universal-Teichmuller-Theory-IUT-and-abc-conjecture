import tmp.sheaf.xif.paper.S2217DedekindFrobTheoremActual

noncomputable section
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2673Probe2Adapted

open LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual

-- test 1: unfold orbitSizeMultiset with explicit instances
example {alpha : Type} [Fintype alpha] (sigma : Equiv.Perm alpha) :
    orbitSizeMultiset sigma =
      @Equiv.Perm.cycleType alpha _ (Classical.decEq alpha) sigma +
        Multiset.replicate (Fintype.card (Function.fixedPoints sigma)) 1 := by
  classical
  simp only [orbitSizeMultiset]

-- test 2: card_fixedPoints rewrite keeps instance
example {alpha : Type} [Fintype alpha] (sigma : Equiv.Perm alpha) :
    orbitSizeMultiset sigma =
      @Equiv.Perm.cycleType alpha _ (Classical.decEq alpha) sigma +
        Multiset.replicate (Fintype.card alpha -
          (@Equiv.Perm.cycleType alpha _ (Classical.decEq alpha) sigma).sum) 1 := by
  classical
  simp only [orbitSizeMultiset]
  rw [Equiv.Perm.card_fixedPoints]

-- test 5: full computation pattern
example {alpha : Type} [Fintype alpha] (sigma : Equiv.Perm alpha) (F : Multiset Nat)
    (hcyc : sigma.cycleType = F.filter (fun n => n != 1))
    (hcard : Fintype.card alpha = F.sum) :
    orbitSizeMultiset sigma = F := by
  classical
  have hcount : F.count 1 = F.sum - (F.filter (fun n => n != 1)).sum := by
    have hid : F.filter (fun n => n != 1) + Multiset.replicate (F.count 1) 1 = F := by
      ext n
      rw [Multiset.count_add, Multiset.count_filter, Multiset.count_replicate]
      by_cases hn : n = 1 <;> simp [hn]
    have h := congrArg Multiset.sum hid
    rw [Multiset.sum_add, Multiset.sum_replicate] at h
    omega
  have hsumF : F.sum = Fintype.card alpha := hcard.symm
  have hcyc' : (@Equiv.Perm.cycleType alpha _ (Classical.decEq alpha) sigma) =
      F.filter (fun n => n != 1) := hcyc
  simp only [orbitSizeMultiset]
  rw [Equiv.Perm.card_fixedPoints, hcyc', hcard]
  rw [show Fintype.card alpha - (F.filter (fun n => n != 1)).sum = F.count 1 by omega]
  ext n
  rw [Multiset.count_add, Multiset.count_filter, Multiset.count_replicate]
  by_cases hn : n = 1 <;> simp [hn]

end LeanFormal.IUT.XiFPaper.S2673Probe2Adapted
end
