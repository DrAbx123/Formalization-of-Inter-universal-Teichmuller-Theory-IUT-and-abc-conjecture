import tmp.sheaf.xif.paper.GenEll06dSection3PowersActual

noncomputable section

namespace LeanFormal.IUT.XiFPaper.GenEll06eSection3ConsequencesActual

open LeanFormal.IUT.XiFPaper.GenEll06bSection3BottomActual
open LeanFormal.IUT.XiFPaper.GenEll06dSection3PowersActual

/-- Consequence: alpha^l = 1 in SL2(Z/l) (because l = 0 in ZMod l); class A. -/
theorem s3135_belyiAlpha_pow_self (l : Nat) [Fact l.Prime] :
    belyiAlpha l ^ l = 1 := by
  have h : ((belyiAlpha l ^ l : Matrix.SpecialLinearGroup (Fin 2) (ZMod l)) :
      Matrix (Fin 2) (Fin 2) (ZMod l)) = !![1, (l : ZMod l); 0, 1] :=
    s3135_belyiAlpha_pow l l
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [h]
  fin_cases i <;> fin_cases j <;> simp [ZMod.natCast_self]
/-- Consequence: beta^l = 1 in SL2(Z/l). -/
theorem s3135_belyiBeta_pow_self (l : Nat) [Fact l.Prime] :
    belyiBeta l ^ l = 1 := by
  have h : ((belyiBeta l ^ l : Matrix.SpecialLinearGroup (Fin 2) (ZMod l)) :
      Matrix (Fin 2) (Fin 2) (ZMod l)) = !![1, 0; (l : ZMod l), 1] :=
    s3135_belyiBeta_pow l l
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [h]
  fin_cases i <;> fin_cases j <;> simp [ZMod.natCast_self]
/-- Consequence: alpha and beta generate a subgroup whose order divides l on each
generator (their l-th powers are trivial). -/
theorem s3135_belyiGenerators_l_torsion (l : Nat) [Fact l.Prime] :
    belyiAlpha l ^ l = 1 ∧ belyiBeta l ^ l = 1 :=
  ⟨s3135_belyiAlpha_pow_self l, s3135_belyiBeta_pow_self l⟩

#check s3135_belyiAlpha_pow_self
#check s3135_belyiBeta_pow_self
#check s3135_belyiGenerators_l_torsion
end LeanFormal.IUT.XiFPaper.GenEll06eSection3ConsequencesActual
end
