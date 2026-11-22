import tmp.sheaf.xif.paper.GenEll06bSection3BottomActual

noncomputable section

namespace LeanFormal.IUT.XiFPaper.GenEll06dSection3PowersActual

open LeanFormal.IUT.XiFPaper.GenEll06bSection3BottomActual

/-- Power formula for the generator alpha in SL2(Z/l): alpha^n = [[1,n],[0,1]]
(elementary class-A matrix induction; supports the Lemma 3.1(i) generation analysis). -/
theorem s3135_belyiAlpha_pow (l : Nat) [Fact l.Prime] (n : Nat) :
    ((belyiAlpha l ^ n : Matrix.SpecialLinearGroup (Fin 2) (ZMod l)) :
        Matrix (Fin 2) (Fin 2) (ZMod l)) = !![1, (n : ZMod l); 0, 1] := by
  induction n with
  | zero =>
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [belyiAlpha]
  | succ n ih =>
      rw [pow_succ]
      change ((belyiAlpha l ^ n : Matrix.SpecialLinearGroup (Fin 2) (ZMod l)) :
          Matrix (Fin 2) (Fin 2) (ZMod l)) * (belyiAlpha l : Matrix (Fin 2) (Fin 2) (ZMod l)) =
        !![1, ((n + 1 : Nat) : ZMod l); 0, 1]
      rw [ih]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [belyiAlpha, Matrix.mul_apply, Fin.sum_univ_two, Nat.cast_succ] <;> ring

/-- Power formula for the generator beta in SL2(Z/l): beta^n = [[1,0],[n,1]]. -/
theorem s3135_belyiBeta_pow (l : Nat) [Fact l.Prime] (n : Nat) :
    ((belyiBeta l ^ n : Matrix.SpecialLinearGroup (Fin 2) (ZMod l)) :
        Matrix (Fin 2) (Fin 2) (ZMod l)) = !![1, 0; (n : ZMod l), 1] := by
  induction n with
  | zero =>
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [belyiBeta]
  | succ n ih =>
      rw [pow_succ]
      change ((belyiBeta l ^ n : Matrix.SpecialLinearGroup (Fin 2) (ZMod l)) :
          Matrix (Fin 2) (Fin 2) (ZMod l)) * (belyiBeta l : Matrix (Fin 2) (Fin 2) (ZMod l)) =
        !![1, 0; ((n + 1 : Nat) : ZMod l), 1]
      rw [ih]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [belyiBeta, Matrix.mul_apply, Fin.sum_univ_two, Nat.cast_succ] <;> ring

#check s3135_belyiAlpha_pow
#check s3135_belyiBeta_pow
end LeanFormal.IUT.XiFPaper.GenEll06dSection3PowersActual
end
