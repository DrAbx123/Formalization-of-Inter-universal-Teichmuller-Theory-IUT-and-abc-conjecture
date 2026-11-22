import tmp.sheaf.xif.paper.S1714AdmissibleActual
import tmp.sheaf.xif.paper.S1715SourceTorsionClauseActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1667AdmissibleCurveActual
open LeanFormal.IUT.XiFPaper.S1714AdmissibleActual
open LeanFormal.IUT.XiFPaper.S1715SourceTorsionClauseActual

namespace LeanFormal.IUT.XiFPaper.S1716D5AssemblyAdapted

theorem S1716Admissible : S1667Admissible := S1714Admissible

theorem S1716Torsion23 :
    PuncturedEllipticCurve.Torsion23Rational
      (S1667Punctured.baseChange S1687Field) :=
  S1708Torsion23Rational

theorem S1716SourceTorsionClause (l : PrimeGeFive)
    (hI : S1715ImageContainsSL2 l) (h5 : l.value ≠ 5) :
    SourceTorsionClause.{0, 0, 0} l :=
  S1715SourceTorsionClause l hI h5

theorem S1716NoClauseAtFive :
    ¬ ∃ T : SourceTorsionClause.{0, 0, 0} (⟨5, by norm_num⟩ : PrimeGeFive),
      T.lTorsionCompatible = S1715LTorsionCompatible _ := by
  intro h
  rcases h with ⟨T, hT⟩
  have hfalse : ¬ S1715LTorsionCompatible (⟨5, by norm_num⟩ : PrimeGeFive) := by
    simpa using S1715LTorsionCompatible_five_false
  exact hfalse (hT ▸ T.lTorsionCompatible_proved)

#print axioms S1716Admissible

end LeanFormal.IUT.XiFPaper.S1716D5AssemblyAdapted
