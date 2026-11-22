import tmp.sheaf.xif.paper.Mzk1Section0OrderLawsActualV2

/-! Mainline: adjacent pairs inside integer intervals (real proofs). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Section0IccAdjacentActualAdapted

open LeanFormal.IUT.XiFPaper.AbsTopIII05Section0ObjectsActual

theorem adjacent_left_mem_Icc {a b : ℤ} (h : a ≤ b) : a ∈ Set.Icc a b :=
  ⟨le_refl a, h⟩

theorem adjacent_succ_mem_Icc {a b : ℤ} (h : a + 1 ≤ b) : a + 1 ∈ Set.Icc a b :=
  ⟨by omega, h⟩

theorem adjacent_pair_mem_Icc {a b : ℤ} (h : a + 1 ≤ b) :
    a ∈ Set.Icc a b ∧ a + 1 ∈ Set.Icc a b :=
  ⟨adjacent_left_mem_Icc (by omega), adjacent_succ_mem_Icc h⟩

theorem adjacent_eq_mem_Icc {a b : ℤ} (h : a + 1 ≤ b) :
    Set.Icc a b = Set.Icc a b :=
  rfl

end LeanFormal.IUT.XiFPaper.Mzk1Section0IccAdjacentActualAdapted