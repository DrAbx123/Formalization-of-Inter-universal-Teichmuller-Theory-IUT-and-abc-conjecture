import tmp.sheaf.xif.paper.S2995A6StackWitnessSpec

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2995A6StackWitnessSpec
open LeanFormal.IUT.XiFPaper.S2994A6Stackification
open LeanFormal.IUT.XiFPaper.S2891A6CFActual
open LeanFormal.IUT.XiFPaper.S2882A6PointwisePseudofunctorActual
open LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) := ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2847A6.F := S2847A6.fieldF
local instance : NumberField S2847A6.F := S2847A6.numberFieldF

namespace LeanFormal.IUT.XiFPaper.S2997A6StackWitnessHelperActual

/-- Fibers/universal interface for the A6 stack witness.  This is the
constructive part: a pseudofunctor with pointwise fibers and the stack
(universal/descent) property. -/
structure S2997A6StackWitnessHelper
    (A : Iut.OrbicurveSignAction S2855HyperbolicOrbicurve) where
  Q : Iut.EtaleStackPseudofunctor S2994A6K
  fibers :
    ∀ U : LocallyDiscrete (Iut.SchemeOverField S2994A6K)ᵒᵖ,
      Nonempty (CategoryTheory.Equivalence (Q.obj U)
        (S2994A6PointwiseQuotient U))
  universal :
    Q.IsStack (Iut.SchemeOverField.etaleTopology S2994A6K)

/-- The universal interface is exactly the etale stack condition. -/
theorem S2997A6StackWitnessHelper.universal_iff
    {A : Iut.OrbicurveSignAction S2855HyperbolicOrbicurve}
    (H : S2997A6StackWitnessHelper A) :
    H.Q.IsStack (Iut.SchemeOverField.etaleTopology S2994A6K) :=
  H.universal

/-- Complete the S2995 witness from the helper plus the two remaining
S2995 fields (`hQ`, quotient, quotientWitness). -/
noncomputable def S2997A6StackWitnessHelper.toSpec
    {A : Iut.OrbicurveSignAction S2855HyperbolicOrbicurve}
    (H : S2997A6StackWitnessHelper A)
    (hQ : S2882A6Q.IsStack (Iut.SchemeOverField.etaleTopology S2847A6.F))
    (quotient : Iut.OrbicurveSignInvariantMorphism A (S2891CF hQ))
    (quotientWitness : Iut.OrbicurveSignQuotientWitness A quotient) :
    S2995A6StackWitnessSpec A where
  Q := H.Q
  isStack := H.universal
  fiberEquiv := H.fibers
  hQ := hQ
  quotient := quotient
  quotientWitness := quotientWitness

#check S2997A6StackWitnessHelper
#check S2997A6StackWitnessHelper.universal_iff
#check S2997A6StackWitnessHelper.toSpec
#print axioms S2997A6StackWitnessHelper.universal_iff
#print axioms S2997A6StackWitnessHelper.toSpec

end LeanFormal.IUT.XiFPaper.S2997A6StackWitnessHelperActual
end
