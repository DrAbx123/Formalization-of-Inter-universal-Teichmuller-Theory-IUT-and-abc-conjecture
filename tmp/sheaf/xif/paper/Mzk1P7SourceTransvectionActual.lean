import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import tmp.sheaf.xif.paper.Mzk1P7TransvectionLargeImageActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P7SourceTransvectionActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open Matrix

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    {S : SourceSignQuotientData A} {C : SourceClauseA A S}
    {B : SourceClauseB A S C}

local notation "Sₗ" => (SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := (1 : Fin 2))
  (by decide) (1 : ZMod l.value))

/-- The concrete transvection matrix in `SL₂(𝔽_l)` used by the source data. -/
def sourceTransvection : SpecialLinearGroup (Fin 2) (ZMod l.value) := Sₗ

theorem sourceTransvection_ne_one : sourceTransvection (l := l) ≠ 1 := by
  intro h
  have h' : ((sourceTransvection (l := l) : SpecialLinearGroup (Fin 2) (ZMod l.value)) :
      Matrix (Fin 2) (Fin 2) (ZMod l.value)) = 1 := by
    simpa using congrArg (fun x : SpecialLinearGroup (Fin 2) (ZMod l.value) =>
      (x : Matrix (Fin 2) (Fin 2) (ZMod l.value))) h
  unfold sourceTransvection at h'
  rw [SpecialLinearGroup.transvection_coe (i := (0 : Fin 2)) (j := (1 : Fin 2))
    (by decide) (1 : ZMod l.value)] at h'
  have h01 := congrFun (congrFun h' (0 : Fin 2)) (1 : Fin 2)
  simp [Matrix.single] at h01
  have hdiv : l.value ∣ 1 :=
    (ZMod.natCast_eq_zero_iff 1 l.value).mp (by simpa using h01)
  have h1 : l.value = 1 := Nat.dvd_one.mp hdiv
  have hge : 5 ≤ l.value := l.ge_five
  rw [h1] at hge
  omega

theorem sourceTransvection_sq :
    (((sourceTransvection (l := l) : SpecialLinearGroup (Fin 2) (ZMod l.value)) :
      Matrix (Fin 2) (Fin 2) (ZMod l.value)) - 1) ^ 2 = 0 := by
  unfold sourceTransvection
  rw [SpecialLinearGroup.transvection_coe (i := (0 : Fin 2)) (j := (1 : Fin 2))
    (by decide) (1 : ZMod l.value)]
  rw [add_sub_cancel_left]
  rw [sq, Matrix.single_mul_single_of_ne (h := by decide)]

/-- Actual transvection source from Clause C `image_contains_SL2`: the canonical
mod-`l` representation contains the concrete transvection. -/
theorem p7_source_transvection_mem (D : SourceClauseC A S C B) :
    (sourceTransvection (l := l)).toGL ∈
      (A.curve.galoisLTorsionMatrixRepresentation l D.torsion_basis).range := by
  have hmem : (sourceTransvection (l := l)).toGL ∈ D.representation.range := by
    exact D.image_contains_SL2 ⟨sourceTransvection (l := l), Subgroup.mem_top _, rfl⟩
  simpa [D.representation_eq_canonical] using hmem

/-- Actual source transvection data: the canonical representation contains the
concrete transvection, which is nontrivial and has square-zero `(T - 1)`. -/
theorem p7_source_transvection_data (D : SourceClauseC A S C B) :
    ∃ T : GL (Fin 2) (ZMod l.value),
      T ∈ (A.curve.galoisLTorsionMatrixRepresentation l D.torsion_basis).range ∧
      T ≠ 1 ∧
      ((T : Matrix (Fin 2) (Fin 2) (ZMod l.value)) - 1) ^ 2 = 0 := by
  refine ⟨(sourceTransvection (l := l)).toGL, p7_source_transvection_mem D, ?_, ?_⟩
  · intro h
    exact sourceTransvection_ne_one (l := l)
      (SpecialLinearGroup.toGL_injective (by simpa using h))
  · rw [SpecialLinearGroup.coe_GL_coe_matrix]
    exact sourceTransvection_sq (l := l)

#print axioms sourceTransvection_ne_one
#print axioms sourceTransvection_sq
#print axioms p7_source_transvection_data

#print axioms p7_source_transvection_mem
end LeanFormal.IUT.XiFPaper.Mzk1P7SourceTransvectionActual