import tmp.sheaf.xif.paper.S1971ActionStackificationActual
import tmp.sheaf.xif.paper.S1964QuotientCFActual
import tmp.sheaf.xif.paper.S1983EtThSignatureBridgeActual
import tmp.sheaf.xif.paper.S2093D9StackActual
import LeanFormal.IUT.IUTI.HodgeTheater.SourceClauseAssemblyUnitsReduction

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1964QuotientCFActual
open LeanFormal.IUT.XiFPaper.S1971ActionStackificationActual
open LeanFormal.IUT.XiFPaper.S1983EtThSignatureBridgeActual
open LeanFormal.IUT.XiFPaper.S1732SourceAssemblyActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2104D9HonestQuotientActual

universe u

variable {l : PrimeGeFive}
variable {A : Iut.OrbicurveSignAction S1726Orbicurve}

/-! ## 1. Exact type of the honest target -/

/-- The honest C_F target is exactly the S1964 quotient-at structure at the
honest signature (0;[2,2,2];1).  This is an abbreviation, not a new target. -/
abbrev S2104HonestCFQuotient := S1964HonestCFQuotient l A

#check S2104HonestCFQuotient
#check S1964HonestCFQuotient
#check S1964CFQuotientAt
#check S1964QuotientStructure

/-! ## 2. Actual construction from a quotient-stack witness -/

/-- The honest-labelled quotient orbicurve built from a stack quotient witness:
the underlying stack fiber is the witness fiber; the signature certificate is
the honest (0;[2,2,2];1) one. -/
noncomputable def S2104CFOfStackWitness
    (W : S1971StackQuotientWitness l A) : Iut.HyperbolicOrbicurve S1726K :=
  realizedHyperbolicOrbicurve S1726K W.cF.stack.fiber W.cF.stack.isStack
    S1964HonestQuotientSignature S1964HonestQuotientSignature_hyperbolic

/-- The sign-invariant quotient morphism transported to the honest-labelled
orbicurve.  Only the stack fiber enters Hom, so the witness morphism is reused
without a new geometric construction. -/
noncomputable def S2104QuotientOfStackWitness
    (W : S1971StackQuotientWitness l A) :
    Iut.OrbicurveSignInvariantMorphism A (S2104CFOfStackWitness W) :=
  { map := W.quotient.map
    invariant := W.quotient.invariant
    cocycle := W.quotient.cocycle }

/-- The bicategorical universal property transported to the honest-labelled
orbicurve.  The witness fields only depend on Hom of stack fibers. -/
noncomputable def S2104WitnessOfStackWitness
    (W : S1971StackQuotientWitness l A) :
    Iut.OrbicurveSignQuotientWitness A (S2104QuotientOfStackWitness W) :=
  { descend := W.witness.descend
    factor := W.witness.factor
    descendTwoCell := W.witness.descendTwoCell
    descendTwoCell_factor := W.witness.descendTwoCell_factor
    twoCell_ext := W.witness.twoCell_ext }

/-- The actual honest C_F quotient structure from an actual quotient-stack
witness.  This does not construct the stack witness; it removes the signature
obstruction from the honest target. -/
noncomputable def S2104HonestCFQuotientOfStackWitness
    (W : S1971StackQuotientWitness l A) :
    S2104HonestCFQuotient (l := l) (A := A) :=
  { cF := S2104CFOfStackWitness W
    cF_signature := rfl
    quotient := S2104QuotientOfStackWitness W
    quotientWitness := S2104WitnessOfStackWitness W }

/-- Conditional actual: a stack quotient witness yields the honest quotient. -/
theorem S2104HonestCFQuotient_of_stackWitness
    (h : Nonempty (S1971StackQuotientWitness l A)) :
    Nonempty (S2104HonestCFQuotient (l := l) (A := A)) :=
  h.elim fun W => ⟨S2104HonestCFQuotientOfStackWitness W⟩

/-- Hence a stack quotient witness gives the S1964 first missing. -/
theorem S2104S1964FirstMissing_of_stackWitness
    (h : Nonempty (S1971StackQuotientWitness l A)) :
    S1964FirstMissing l A :=
  S1964FirstMissing_ofHonest (S2104HonestCFQuotient_of_stackWitness h)

/-- Hence a stack quotient witness gives the S1983 honest first missing. -/
theorem S2104S1983FirstMissing_of_stackWitness
    (h : Nonempty (S1971StackQuotientWitness l A)) :
    S1983FirstMissing l A :=
  (S1983FirstMissing_iff_honest (l := l) (A := A)).mpr
    (S2104HonestCFQuotient_of_stackWitness h)

/-! ## 3. The exact first missing -/

/-- The exact remaining input for the honest sign quotient: an actual
S1971 stack quotient witness.  This contains the actual C_F orbicurve, the
sign-invariant quotient morphism, the universal property, and the pointwise
identification of its fibers with the action-groupoid quotient. -/
def S2104HonestQuotientFirstMissing : Prop :=
  Nonempty (S1971StackQuotientWitness l A)

/-- The exact first missing is exactly the missing quotient-stack witness; no
separate signature label gap remains. -/
theorem S2104HonestQuotientFirstMissing_iff :
    S2104HonestQuotientFirstMissing (l := l) (A := A) ↔
      Nonempty (S1971StackQuotientWitness l A) :=
  Iff.rfl

#print axioms S2104CFOfStackWitness
#print axioms S2104QuotientOfStackWitness
#print axioms S2104WitnessOfStackWitness
#print axioms S2104HonestCFQuotientOfStackWitness
#print axioms S2104HonestCFQuotient_of_stackWitness
#print axioms S2104S1964FirstMissing_of_stackWitness
#print axioms S2104S1983FirstMissing_of_stackWitness

end LeanFormal.IUT.XiFPaper.S2104D9HonestQuotientActual

end
