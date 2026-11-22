import tmp.sheaf.xif.paper.Mzk1P7SourceTransvectionActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P7SourceHlineActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open Matrix

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    {S : SourceSignQuotientData A} {C : SourceClauseA A S}
    {B : SourceClauseB A S C}

/-- Generic SL2 no-invariant-line step. -/
theorem p7_sl2_no_invariant_line
    (G : Subgroup (GL (Fin 2) (ZMod l.value)))
    (hSL : Subgroup.map Matrix.SpecialLinearGroup.toGL
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value))) ≤ G) :
    ∀ v : Fin 2 → ZMod l.value, v ≠ 0 →
      ∃ g ∈ G, ∀ c : ZMod l.value,
        (g : Matrix (Fin 2) (Fin 2) (ZMod l.value)) *ᵥ v ≠ c • v := by
  haveI : Fact l.value.Prime := ⟨l.prime⟩
  intro v hv
  by_cases hv1 : v 1 = 0
  · have hv0 : v 0 ≠ 0 := by
      intro h0
      apply hv
      ext i
      fin_cases i <;> simp [hv1, h0]
    let A21 : Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value) :=
      Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := (0 : Fin 2))
        (by decide) (1 : ZMod l.value)
    refine ⟨A21.toGL, hSL ⟨A21, Subgroup.mem_top _, rfl⟩, ?_⟩
    intro c heq
    have h0 := congrFun heq 0
    have h1 := congrFun heq 1
    have hact : ((A21.toGL : Matrix (Fin 2) (Fin 2) (ZMod l.value)) *ᵥ v) =
        v + (v 0) • Pi.single (1 : Fin 2) (1 : ZMod l.value) := by
      change ((Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := (0 : Fin 2))
        (by decide) (1 : ZMod l.value) : Matrix (Fin 2) (Fin 2) (ZMod l.value)) *ᵥ v) =
        v + (v 0) • Pi.single (1 : Fin 2) (1 : ZMod l.value)
      rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_mulVec,
        Matrix.one_mulVec, Matrix.single_mulVec_eq]
      simp
    have ha0 := congrFun hact 0
    have ha1 := congrFun hact 1
    rw [ha0] at h0
    rw [ha1] at h1
    simp [Pi.add_apply, Pi.smul_apply, Pi.single] at h0 h1
    have hc : c = 1 := by
      apply mul_right_cancel₀ hv0
      simpa using h0.symm
    simp [hv1, hc] at h1
    exact hv0 (by simpa using h1)
  · let A12 : Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value) :=
      Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := (1 : Fin 2))
        (by decide) (1 : ZMod l.value)
    refine ⟨A12.toGL, hSL ⟨A12, Subgroup.mem_top _, rfl⟩, ?_⟩
    intro c heq
    have h0 := congrFun heq 0
    have h1 := congrFun heq 1
    have hact : ((A12.toGL : Matrix (Fin 2) (Fin 2) (ZMod l.value)) *ᵥ v) =
        v + (v 1) • Pi.single (0 : Fin 2) (1 : ZMod l.value) := by
      change ((Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := (1 : Fin 2))
        (by decide) (1 : ZMod l.value) : Matrix (Fin 2) (Fin 2) (ZMod l.value)) *ᵥ v) =
        v + (v 1) • Pi.single (0 : Fin 2) (1 : ZMod l.value)
      rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_mulVec,
        Matrix.one_mulVec, Matrix.single_mulVec_eq]
      simp
    have ha0 := congrFun hact 0
    have ha1 := congrFun hact 1
    rw [ha0] at h0
    rw [ha1] at h1
    simp [Pi.add_apply, Pi.smul_apply, Pi.single] at h0 h1
    have hc : c = 1 := by
      apply mul_right_cancel₀ hv1
      simpa using h1.symm
    simp [hc] at h0
    have : v 1 = 0 := by simpa using h0
    exact hv1 this

theorem p7_source_no_invariant_line (D : SourceClauseC A S C B) :
    ∀ v : Fin 2 → ZMod l.value, v ≠ 0 →
      ∃ g ∈ (A.curve.galoisLTorsionMatrixRepresentation l D.torsion_basis).range,
        ∀ c : ZMod l.value,
          (g : Matrix (Fin 2) (Fin 2) (ZMod l.value)) *ᵥ v ≠ c • v := by
  have h := p7_sl2_no_invariant_line (l := l) D.representation.range D.image_contains_SL2
  simpa [D.representation_eq_canonical] using h


/-- Large-image instance from Clause C: the actual transvection and no-line data
give the full `SL₂` image in the canonical mod-`l` representation range. -/
theorem p7_largeImage_source (D : SourceClauseC A S C B)
    (M : Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value)) :
    M.toGL ∈ (A.curve.galoisLTorsionMatrixRepresentation l D.torsion_basis).range :=
  LeanFormal.IUT.XiFPaper.Mzk1P7TransvectionLargeImageActual.p7_sl2_le_range_of_transvection
    A.curve D.torsion_basis (LeanFormal.IUT.XiFPaper.Mzk1P7SourceTransvectionActual.p7_source_transvection_data D)
    (p7_source_no_invariant_line D) M

#print axioms p7_largeImage_source

#print axioms p7_source_no_invariant_line
end LeanFormal.IUT.XiFPaper.Mzk1P7SourceHlineActual