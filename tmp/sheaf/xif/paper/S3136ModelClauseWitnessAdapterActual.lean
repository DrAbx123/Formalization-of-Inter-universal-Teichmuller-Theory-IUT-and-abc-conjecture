import tmp.sheaf.xif.paper.S3136ModelSourceClauseActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceClauseConstructors

/-! # Stage-4 host: SourceClauseConstructionWitness -> concrete clause data adapter

Source anchors: IUT I, Definition 3.1 (initial Theta data: arithmetic, six-tuple,
clauses A--F over the sign quotient); IUT I, Example 3.2, (iv) (concrete
Gaussian arithmetic).

CONSUMER: hull's S3132ConcreteSourceVFormInstantiatedActual and qpilot's model
skeleton.  Transporting a witness's dependent fields along an arithmetic equality
is not type-correct in general, so this adapter keeps the witness arithmetic and
records the concrete-Gaussian equality as data:
* LGPConcreteClauseData l: arithmetic + proof it is the concrete Gaussian
  arithmetic + SourceInitialThetaTuple + clauses A--F over that arithmetic;
* lgpConcreteClauseData_of_witness: from a witness plus the arithmetic equality;
* lgpConcreteClauseData_toNativeData: the corresponding
  SourceNativeInitialThetaData, with arithmetic theorem;
* lgpConcreteClauseData_of_witness_toNativeData: composed form for consumers.

LABEL: prerequisite component + exact interface; NOT a paper object claim.
Registry frozen; new file only. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136ModelClauseWitnessAdapterActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource

variable {l : PrimeGeFive}

/-- Concrete clause data over an arithmetic root, with proof that the root is the
concrete Example 3.6 Gaussian arithmetic. -/
structure LGPConcreteClauseData (l : PrimeGeFive) where
  arithmetic : InitialThetaArithmeticData l
  arithmetic_is_concrete :
    arithmetic = concreteGaussianInitialThetaArithmeticData l
  tuple : SourceInitialThetaTuple arithmetic
  clauseA : SourceClauseA arithmetic tuple.source
  clauseB : SourceClauseB arithmetic tuple.source clauseA
  clauseC : SourceClauseC arithmetic tuple.source clauseA clauseB
  clauseD : SourceClauseD arithmetic tuple.source clauseA clauseB clauseC
  clauseE : SourceClauseE arithmetic tuple.source clauseA clauseB clauseC clauseD
  clauseF : SourceClauseF arithmetic tuple.source clauseA clauseB clauseC clauseD
    clauseE

/-- Adapter from a clause-construction witness plus the concrete-arithmetic
equality. -/
def lgpConcreteClauseData_of_witness
    (W : SourceClauseConstructionWitness.{0} l)
    (hA : W.arithmetic = concreteGaussianInitialThetaArithmeticData l) :
    LGPConcreteClauseData l where
  arithmetic := W.arithmetic
  arithmetic_is_concrete := hA
  tuple := W.sourceData.tuple
  clauseA := W.sourceData.clauseA
  clauseB := W.sourceData.clauseB
  clauseC := W.sourceData.clauseC
  clauseD := W.sourceData.clauseD
  clauseE := W.sourceData.clauseE
  clauseF := W.sourceData.clauseF

/-- The native initial-Theta datum carried by the concrete clause data. -/
def lgpConcreteClauseData_toNativeData (M : LGPConcreteClauseData l) :
    SourceNativeInitialThetaData.{0} l where
  arithmetic := M.arithmetic
  tuple := M.tuple
  clauseA := M.clauseA
  clauseB := M.clauseB
  clauseC := M.clauseC
  clauseD := M.clauseD
  clauseE := M.clauseE
  clauseF := M.clauseF

/-- The native datum has the concrete Gaussian arithmetic. -/
theorem lgpConcreteClauseData_toNativeData_arithmetic
    (M : LGPConcreteClauseData l) :
    (lgpConcreteClauseData_toNativeData M).arithmetic =
      concreteGaussianInitialThetaArithmeticData l :=
  M.arithmetic_is_concrete

/-- Composed form: witness + arithmetic equality -> native datum with arithmetic
proof. -/
def lgpConcreteClauseData_of_witness_toNativeData
    (W : SourceClauseConstructionWitness.{0} l)
    (hA : W.arithmetic = concreteGaussianInitialThetaArithmeticData l) :
    { D : SourceNativeInitialThetaData.{0} l //
        D.arithmetic = concreteGaussianInitialThetaArithmeticData l } :=
  ⟨lgpConcreteClauseData_toNativeData (lgpConcreteClauseData_of_witness W hA),
    lgpConcreteClauseData_toNativeData_arithmetic
      (lgpConcreteClauseData_of_witness W hA)⟩

#check LGPConcreteClauseData
#check lgpConcreteClauseData_of_witness
#check lgpConcreteClauseData_toNativeData
#check lgpConcreteClauseData_toNativeData_arithmetic
#check lgpConcreteClauseData_of_witness_toNativeData

end LeanFormal.IUT.XiFPaper.S3136ModelClauseWitnessAdapterActual
end