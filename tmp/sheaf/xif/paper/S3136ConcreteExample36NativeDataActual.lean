import LeanFormal.IUT.IUTI.InitialTheta.SourceCompletion
import LeanFormal.IUT.IUTI.InitialTheta.ConcreteFinitePlaceBoundary

/-! # Stage-4 host: concrete Example 3.6 native initial-Theta data (route + exact missing)

Source anchors: IUT I, Definition 3.1 (initial Theta data, six-tuple with
clauses A--F); IUT I, Example 3.2, (iv) (the concrete Gaussian arithmetic);
IUT III, Definition 3.8, (i) (the stage data used downstream).

CONSUMER: hull's paper-route Theta side needs a concrete
`SourceNativeInitialThetaData` for the Example 3.6 stage.  The existing
`SourceCompletion.toSourceNativeInitialThetaData` (SourceCompletion.lean:601)
turns a full SourceCompletion into the native data.  The piece that is genuinely
NOT constructed in the tree is the concrete Example-3.6 *tuple + clauses A--F*
(hull confirms HodgeTheater has only arithmetic/primeStrip/thetaPacket, and the
paper-side witnesses are conditional).

This file provides:
* LGPConcreteExample36NativeDataMissing: the exact concrete DATA needed (a
  SourceInitialThetaTuple over the concrete Gaussian arithmetic plus clauses
  A--F), as a data structure (not opaque Props);
* lgpConcreteExample36NativeData: the constructive passage from that data to a
  concrete SourceNativeInitialThetaData (no faking, no Prop fields);
* lgpConcreteExample36NativeData_of_completion: the existing route via
  SourceCompletion;
* arithmetic/route projections and the required-route notes
  (SourceClauseAssembly / SourceClauseConstructionWitness).

LABEL: prerequisite component + exact missing data; NOT a paper object.
Registry frozen; new file only. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136ConcreteExample36NativeDataActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource

/-- The concrete Gaussian arithmetic of Example 3.6. -/
abbrev lgpConcreteExample36Arithmetic :
    InitialThetaArithmeticData.{0} l :=
  concreteGaussianInitialThetaArithmeticData l

/-- The EXACT concrete data missing for the Example 3.6 native initial-Theta
datum: a SourceInitialThetaTuple over the concrete Gaussian arithmetic together
with the six clauses A--F of IUT I, Definition 3.1.  These are data fields (not
opaque propositions): an inhabitant would be the genuine concrete tuple/clause
construction. -/
structure LGPConcreteExample36NativeDataMissing (l : PrimeGeFive) where
  tuple : SourceInitialThetaTuple (concreteGaussianInitialThetaArithmeticData l)
  clauseA : SourceClauseA (concreteGaussianInitialThetaArithmeticData l)
    tuple.source
  clauseB : SourceClauseB (concreteGaussianInitialThetaArithmeticData l)
    tuple.source clauseA
  clauseC : SourceClauseC (concreteGaussianInitialThetaArithmeticData l)
    tuple.source clauseA clauseB
  clauseD : SourceClauseD (concreteGaussianInitialThetaArithmeticData l)
    tuple.source clauseA clauseB clauseC
  clauseE : SourceClauseE (concreteGaussianInitialThetaArithmeticData l)
    tuple.source clauseA clauseB clauseC clauseD
  clauseF : SourceClauseF (concreteGaussianInitialThetaArithmeticData l)
    tuple.source clauseA clauseB clauseC clauseD clauseE

/-- Constructive passage: the exact missing concrete data yields a concrete
Example 3.6 SourceNativeInitialThetaData. -/
def lgpConcreteExample36NativeData
    (M : LGPConcreteExample36NativeDataMissing l) :
    SourceNativeInitialThetaData.{0} l where
  arithmetic := concreteGaussianInitialThetaArithmeticData l
  tuple := M.tuple
  clauseA := M.clauseA
  clauseB := M.clauseB
  clauseC := M.clauseC
  clauseD := M.clauseD
  clauseE := M.clauseE
  clauseF := M.clauseF

/-- The constructed datum has the concrete Gaussian arithmetic. -/
theorem lgpConcreteExample36NativeData_arithmetic
    (M : LGPConcreteExample36NativeDataMissing l) :
    (lgpConcreteExample36NativeData M).arithmetic =
      concreteGaussianInitialThetaArithmeticData l := rfl

/-- Existing route: a full SourceCompletion gives the native initial-Theta data. -/
def lgpConcreteExample36NativeData_of_completion
    (C : SourceCompletion.{0} l) :
    SourceNativeInitialThetaData.{0} l :=
  C.toSourceNativeInitialThetaData

#check lgpConcreteExample36Arithmetic
#check LGPConcreteExample36NativeDataMissing
#check lgpConcreteExample36NativeData
#check lgpConcreteExample36NativeData_arithmetic
#check lgpConcreteExample36NativeData_of_completion

end LeanFormal.IUT.XiFPaper.S3136ConcreteExample36NativeDataActual
end