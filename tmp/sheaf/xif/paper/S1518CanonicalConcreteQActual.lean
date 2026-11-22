import LeanFormal.IUT.IUTII.Frobenioid.Example36TateUniformization
import LeanFormal.IUT.IUTI.InitialTheta.ConcreteArithmeticExample

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S1518CanonicalConcreteQActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.TateUniformization

local instance s1518GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-- The explicit actual q=5 Tate parameter in Q_5 has norm 1/5. -/
theorem S1518ActualFiveQ_norm :
    ‖concreteFiveTateParameter‖ = ((5 : Real)⁻¹) := by
  rw [concreteFiveTateParameter_norm,
    SourceTheaterCarrier.gaussianFiveThetaQ_eq_inv_five]

/-- The explicit actual q=5 is contracting. -/
theorem S1518ActualFiveQ_norm_lt_one :
    ‖concreteFiveTateParameter‖ < 1 := by
  rw [S1518ActualFiveQ_norm]
  norm_num

/-- Exact first required object: a q-candidate at the concrete rational place
above 5, with norm 1/5.  No inhabitant is asserted; the explicit Q_5 Tate
parameter still needs its actual identification/transport into the completion
carrier `Completion concreteFivePlace`. -/
def S1518CanonicalFiveQCandidateRequired : Type :=
  {q : FinitePlaceQCandidate concreteFivePlace // ‖q.q‖ = ((5 : Real)⁻¹)}

/-- Exact first required Gaussian-completion object: a q-candidate at the
concrete Gaussian place above 5, with norm 1/5. -/
def S1518CanonicalGaussianQRequired : Type :=
  {q : FinitePlaceQCandidate concreteGaussianFivePlace //
    ‖q.q‖ = ((5 : Real)⁻¹)}

/-- Exact first identification: the canonical q candidate must be identified
with the Classical.choice candidate concreteQCandidate (not asserted). -/
def S1518CanonicalQIdentificationRequired : Prop :=
  ∃ q : FinitePlaceQCandidate concreteFivePlace,
    ‖q.q‖ = ((5 : Real)⁻¹)

end LeanFormal.IUT.XiFPaper.S1518CanonicalConcreteQActual

end
