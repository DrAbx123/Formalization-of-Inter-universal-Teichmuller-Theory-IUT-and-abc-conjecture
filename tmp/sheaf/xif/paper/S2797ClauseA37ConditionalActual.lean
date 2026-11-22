import tmp.sheaf.xif.paper.S2786SignQuotientActual
import tmp.sheaf.xif.paper.S2793FieldOfModuliQiActual
import tmp.sheaf.xif.paper.S2766MaximalSolvableTopActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2786SignQuotientActual
open LeanFormal.IUT.XiFPaper.S2766MaximalSolvableTopActual
open LeanFormal.IUT.XiFPaper.S2782Curve37a1Actual
open LeanFormal.IUT.XiFPaper.S2793FieldOfModuliQiActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.NumberFieldFinitePlace
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2797ClauseA37ConditionalActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-- Field-of-moduli datum j = 110592/37 for 37a1 over Q(i). -/
noncomputable def S2797FieldOfModuli :
    SourceFieldOfModuli S2786Arithmetic where
  jModuli := (110592 / 37 : GaussianField)
  algebraMap_jModuli := by
    change (110592 / 37 : GaussianField) = E37Qi.j
    rw [E37Qi_j]

/-- Conditional SourceClauseA for E37/Q(i): the only remaining input is stable
reduction at every finite place; field of moduli and maximal solvable
extension are actual. -/
noncomputable def S2797ClauseA
    (S : SourceSignQuotientData S2786Arithmetic)
    (hstable : ∀ p : NumberField.FinitePlace S2786Arithmetic.F,
      S2786Arithmetic.curve.HasStableReductionAt p) :
    SourceClauseA S2786Arithmetic S where
  stable_reduction_nonarchimedean := hstable
  field_of_moduli := S2797FieldOfModuli
  maximal_solvable_extension := ⊤
  maximal_solvable_property := top_isFiniteSolvableGaloisSubextension
  maximal_solvable_contains := maximalSolvableContains_top

#check S2797FieldOfModuli
#check S2797ClauseA
#print axioms S2797FieldOfModuli
#print axioms S2797ClauseA

end LeanFormal.IUT.XiFPaper.S2797ClauseA37ConditionalActual
end
