import tmp.sheaf.xif.paper.S3105ConcreteSplitJ
import tmp.sheaf.xif.paper.S1280SourceDefinition31Actual
import tmp.sheaf.xif.paper.S2766MaximalSolvableTopActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceClauseConstructors

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S3105ConcreteSplitJ
open LeanFormal.IUT.XiFPaper.S2766MaximalSolvableTopActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S3105FieldOfModuli

local instance : Fact (Irreducible
    (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-- The actual S1280 arithmetic input. -/
abbrev S1280A (l : PrimeGeFive) := S1280Arithmetic l

/-- Field of moduli for the actual S1280 curve, whose j-invariant is -1/10805. -/
noncomputable def S3105FieldOfModuli (l : PrimeGeFive) :
    SourceFieldOfModuli (S1280A l) where
  jModuli := (-1 / 10805 : GaussianField)
  algebraMap_jModuli := by
    change (-1 / 10805 : GaussianField) =
      (concreteSplitPuncturedCurve.baseChange GaussianField).jInvariant
    rw [S3105ConcreteSplitJ]
    norm_num

/-- Conditional ClauseA: field of moduli and maximal solvable extension are
actual; stable reduction is supplied as the explicit remaining input. -/
noncomputable def S3105ClauseA (l : PrimeGeFive)
    (S : SourceSignQuotientData (S1280A l))
    (hred : ∀ p : NumberField.FinitePlace (S1280A l).F,
      (S1280A l).curve.HasGoodReductionAt p ∨
        (S1280A l).curve.HasMultiplicativeReductionAt p) :
    SourceClauseA (S1280A l) S :=
  SourceClauseA.ofGoodOrMultiplicativeReduction hred
    (S3105FieldOfModuli l)
    (⊤ : IntermediateField (S1280A l).Fmod (S1280A l).F)
    (top_isFiniteSolvableGaloisSubextension (k := GaussianField))
    (fun _ _ => le_top)

#check S3105FieldOfModuli
#check S3105ClauseA
#print axioms S3105FieldOfModuli

end LeanFormal.IUT.XiFPaper.S3105FieldOfModuli
end
