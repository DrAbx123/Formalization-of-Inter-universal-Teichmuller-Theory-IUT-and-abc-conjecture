import tmp.sheaf.xif.paper.S1496OScalarConcreteActual
import tmp.sheaf.xif.paper.ConcreteC3DonorActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S1506ConcreteQNormActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source.ConcreteC3DonorActual
open LeanFormal.IUT.XiFPaper.S1496OScalarConcreteActual
open LeanFormal.IUT.XiFPaper.S1391C3LSourcePilotActual

universe u
variable {l : PrimeGeFive}
variable {I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)}
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)

/-- Actual q-candidate law: the concrete C3 q is nonzero. -/
theorem s1506ConcreteQ_ne_zero :
    (concreteQCandidate I place).q ≠ 0 :=
  (concreteQCandidate I place).q_ne_zero

/-- Actual q-candidate law: the completed valuation of the concrete q is < 1. -/
theorem s1506ConcreteQValuation_lt_one :
    (Valued.v (concreteQCandidate I place).q : WithZero (Multiplicative Int)) < 1 :=
  (concreteQCandidate I place).valuation_lt_one

/-- Actual norm consequence of the q-candidate law: the concrete q has norm < 1. -/
theorem s1506ConcreteQNorm_lt_one :
    ‖(concreteQCandidate I place).q‖ < 1 :=
  (Valued.toNormedField.norm_lt_one_iff).mpr
    (concreteQCandidate I place).valuation_lt_one

/-- Exact first computation lemma: the concrete q has norm exactly 1/5.  The
q-candidate structure supplies only |q|<1, not this exact norm; no inhabitant
is asserted. -/
def S1506ConcreteQNormExact : Prop :=
  ‖(concreteQCandidate I place).q‖ = ((5 : Real)⁻¹)

/-- Exact second computation lemma: the concrete bad-place q family satisfies
the source-bad-q formula.  This is the S1496 source-side exact input. -/
def S1506ConcreteSourceBadQExact : Prop :=
  -sourceBadQAbsLog I.initial = Real.log ‖(concreteQCandidate I place).q‖

end LeanFormal.IUT.XiFPaper.S1506ConcreteQNormActual

end
