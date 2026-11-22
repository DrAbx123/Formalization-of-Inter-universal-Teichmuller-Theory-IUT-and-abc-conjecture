import tmp.sheaf.xif.paper.GenEll06bSection3BottomActual

noncomputable section

namespace LeanFormal.IUT.XiFPaper.GenEll06cSection3ProvableActual

open LeanFormal.IUT.XiFPaper.GenEll06bSection3BottomActual

/-- The generator alpha is nontrivial: its (0,1)-entry is 1, while the identity
matrix has (0,1)-entry 0 (elementary class-A fact in the Lemma 3.1 context). -/
theorem s3135_belyiAlpha_ne_one (l : Nat) [Fact l.Prime] :
    belyiAlpha l ≠ 1 := by
  haveI : NeZero l := ⟨(Fact.out : Nat.Prime l).ne_zero⟩
  intro h
  have h01 := congrArg
    (fun x : Matrix.SpecialLinearGroup (Fin 2) (ZMod l) =>
      (x : Matrix (Fin 2) (Fin 2) (ZMod l)) 0 1) h
  simp [belyiAlpha] at h01

/-- The generator beta is nontrivial. -/
theorem s3135_belyiBeta_ne_one (l : Nat) [Fact l.Prime] :
    belyiBeta l ≠ 1 := by
  haveI : NeZero l := ⟨(Fact.out : Nat.Prime l).ne_zero⟩
  intro h
  have h10 := congrArg
    (fun x : Matrix.SpecialLinearGroup (Fin 2) (ZMod l) =>
      (x : Matrix (Fin 2) (Fin 2) (ZMod l)) 1 0) h
  simp [belyiBeta] at h10

/-- The product alpha*beta has the explicit matrix form [[2,1],[1,1]] (elementary
class-A matrix computation in the SL2 generators). -/
theorem s3135_belyiAlpha_mul_belyiBeta (l : Nat) [Fact l.Prime] :
    ((belyiAlpha l * belyiBeta l : Matrix.SpecialLinearGroup (Fin 2) (ZMod l)) :
        Matrix (Fin 2) (Fin 2) (ZMod l)) = !![2, 1; 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [belyiAlpha, belyiBeta, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

#check s3135_belyiAlpha_ne_one
#check s3135_belyiBeta_ne_one
#check s3135_belyiAlpha_mul_belyiBeta
end LeanFormal.IUT.XiFPaper.GenEll06cSection3ProvableActual
end
-- bump-4
