/- U-C 前置：`NumberField ↥(FtpdLam lam)` 实例（sophie 的 D2 需要）。

`FtpdLam lam = adjoin ℚ {jOfLam lam, lam}`；当 `lam` 代数时，`jOfLam lam` 是
`lam` 的有理函数，故 `FtpdLam lam = adjoin ℚ {lam}` 有限维，得到 `NumberField`。
-/
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import tmp.sheaf.xif.paper.Mzk1ULTripodalFieldActual

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ULTripodalNumberField

open LeanFormal.IUT.XiFPaper.Mzk1ULTripodalFieldActual

/-- `jOfLam lam` 属于 `adjoin ℚ {lam}`（有理函数对域运算封闭）。 -/
private lemma jOfLam_mem_adjoin (lam : ℂ) :
    jOfLam lam ∈ IntermediateField.adjoin ℚ ({lam} : Set ℂ) := by
  set A := IntermediateField.adjoin ℚ ({lam} : Set ℂ)
  have hlam : lam ∈ A := IntermediateField.mem_adjoin_of_mem ℚ (Set.mem_singleton lam)
  have h256 : (256 : ℂ) ∈ A := by
    simpa using A.natCast_mem 256
  have hsq : lam ^ 2 ∈ A := by
    rw [pow_two]
    exact A.mul_mem hlam hlam
  have h1 : (1 : ℂ) ∈ A := A.one_mem
  have hbase : (1 - lam + lam ^ 2) ∈ A := A.add_mem (A.sub_mem h1 hlam) hsq
  have hcube : (1 - lam + lam ^ 2) ^ 3 ∈ A := by
    rw [pow_succ, pow_two]
    exact A.mul_mem (A.mul_mem hbase hbase) hbase
  have hnum : (256 : ℂ) * (1 - lam + lam ^ 2) ^ 3 ∈ A := A.mul_mem h256 hcube
  have hden : lam ^ 2 * (1 - lam) ^ 2 ∈ A := by
    have h2 : (1 - lam) ^ 2 ∈ A := by
      rw [pow_two]
      exact A.mul_mem (A.sub_mem h1 hlam) (A.sub_mem h1 hlam)
    exact A.mul_mem hsq h2
  unfold jOfLam
  exact A.div_mem hnum hden

/-- `FtpdLam lam ≤ adjoin ℚ {lam}`。 -/
private lemma FtpdLam_le_adjoin (lam : ℂ) :
    FtpdLam lam ≤ IntermediateField.adjoin ℚ ({lam} : Set ℂ) := by
  show IntermediateField.adjoin ℚ ({jOfLam lam, lam} : Set ℂ) ≤ _
  rw [IntermediateField.adjoin_le_iff]
  intro x hx
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact jOfLam_mem_adjoin lam
  · exact IntermediateField.subset_adjoin ℚ _ (by simp)

/-- `adjoin ℚ {lam} ≤ FtpdLam lam`。 -/
private lemma adjoin_le_FtpdLam (lam : ℂ) :
    IntermediateField.adjoin ℚ ({lam} : Set ℂ) ≤ FtpdLam lam := by
  show IntermediateField.adjoin ℚ ({lam} : Set ℂ)
    ≤ IntermediateField.adjoin ℚ ({jOfLam lam, lam} : Set ℂ)
  rw [IntermediateField.adjoin_le_iff]
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  rcases hx with rfl
  exact IntermediateField.subset_adjoin ℚ _ (by simp)

/-- **`NumberField` instance** for `↥(FtpdLam lam)` when `lam` is algebraic over ℚ. -/
theorem numberField_FtpdLam (lam : ℂ) (hlam : IsAlgebraic ℚ lam) :
    NumberField ↥(FtpdLam lam) where
  to_charZero := inferInstance
  to_finiteDimensional := by
    have hEq : FtpdLam lam = IntermediateField.adjoin ℚ ({lam} : Set ℂ) :=
      le_antisymm (FtpdLam_le_adjoin lam) (adjoin_le_FtpdLam lam)
    have hfd : FiniteDimensional ℚ ↥(IntermediateField.adjoin ℚ ({lam} : Set ℂ)) :=
      IntermediateField.adjoin.finiteDimensional (isAlgebraic_iff_isIntegral.mp hlam)
    rw [hEq]
    exact hfd

example (lam : ℂ) (hlam : IsAlgebraic ℚ lam) : Module.finrank ℚ ↥(FtpdLam lam) ≠ 0 := by
  letI := numberField_FtpdLam lam hlam
  exact Module.finrank_pos.ne'


/-- `NumberField` instance for the moduli field `↥(FmodLam lam)` when `lam` is algebraic. -/
theorem numberField_FmodLam (lam : ℂ) (hlam : IsAlgebraic ℚ lam) :
    NumberField ↥(FmodLam lam) where
  to_charZero := inferInstance
  to_finiteDimensional := by
    have hle : FmodLam lam ≤ IntermediateField.adjoin ℚ ({lam} : Set ℂ) := by
      show IntermediateField.adjoin ℚ ({jOfLam lam} : Set ℂ) ≤ _
      rw [IntermediateField.adjoin_le_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rcases hx with rfl
      exact jOfLam_mem_adjoin lam
    haveI : FiniteDimensional ℚ ↥(IntermediateField.adjoin ℚ ({lam} : Set ℂ)) :=
      IntermediateField.adjoin.finiteDimensional (isAlgebraic_iff_isIntegral.mp hlam)
    let incl : ↥(FmodLam lam) →ₗ[ℚ] ↥(IntermediateField.adjoin ℚ ({lam} : Set ℂ)) :=
      { toFun := fun x => ⟨x.1, hle x.2⟩
        map_add' := by
          intro x y
          ext
          simp
        map_smul' := by
          intro c x
          ext
          simp }
    refine Module.Finite.of_injective incl ?_
    intro x y h
    apply Subtype.ext
    have h' := congrArg (fun z : ↥(IntermediateField.adjoin ℚ ({lam} : Set ℂ)) => (z : ℂ)) h
    simpa [incl] using h'

#print axioms numberField_FtpdLam
#print axioms numberField_FmodLam

end LeanFormal.IUT.XiFPaper.ULTripodalNumberField
end