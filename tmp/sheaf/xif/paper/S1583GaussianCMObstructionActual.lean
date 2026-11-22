import tmp.sheaf.xif.paper.S1558KernelFieldDegreeActual
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
noncomputable section
open Matrix
namespace LeanFormal.IUT.XiFPaper.S1583GaussianCMObstructionActual
variable {l : PrimeGeFive}
def S1583J : Matrix (Fin 2) (Fin 2) (ZMod l.value) := !![0, -1; 1, 0]
def S1583U : Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value) :=
  ⟨!![1, 1; 0, 1], by rw [Matrix.det_fin_two]; norm_num⟩
theorem S1583U_not_commute_J :
    ¬ Commute (S1583U (l := l) : Matrix (Fin 2) (Fin 2) (ZMod l.value))
      (S1583J (l := l)) := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  simp [S1583U, S1583J, Matrix.mul_apply, Fin.sum_univ_two] at h00
  have hdvd : l.value ∣ 1 := by
    apply (ZMod.natCast_eq_zero_iff 1 l.value).mp
    simpa using h00
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  have h5 := l.ge_five
  omega
variable {F : Type*} [Field F] [CharZero F]
variable (X : PuncturedEllipticCurve F) (basis :
  (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value] X.LTorsion l)
theorem S1583_not_imageContainsSL2_of_centralizer
    (hcomm : ∀ σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F,
      Commute ((X.galoisLTorsionMatrixRepresentation l basis σ :
          Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value)) :
            Matrix (Fin 2) (Fin 2) (ZMod l.value))
        (S1583J (l := l))) :
    ¬ PuncturedEllipticCurve.LTorsionImageContainsSL2 X l basis := by
  intro hSL2
  obtain ⟨σ, hσ⟩ := hSL2 (S1583U (l := l))
  have hc := hcomm σ
  rw [hσ] at hc
  apply S1583U_not_commute_J (l := l)
  simpa [Matrix.SpecialLinearGroup.coe_GL_coe_matrix] using hc
def S1583GaussianCMActionCommutes : Prop :=
  ∀ σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F,
    Commute ((X.galoisLTorsionMatrixRepresentation l basis σ :
        Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value)) :
          Matrix (Fin 2) (Fin 2) (ZMod l.value))
      (S1583J (l := l))
theorem S1583Gaussian_not_imageContainsSL2
    (h : S1583GaussianCMActionCommutes X basis) :
    ¬ PuncturedEllipticCurve.LTorsionImageContainsSL2 X l basis :=
  S1583_not_imageContainsSL2_of_centralizer X basis h
end LeanFormal.IUT.XiFPaper.S1583GaussianCMObstructionActual
end
