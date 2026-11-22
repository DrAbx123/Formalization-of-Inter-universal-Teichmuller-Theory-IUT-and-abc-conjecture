import LeanFormal.IUT.IUTI.InitialTheta.ConcreteFinitePlaceBoundary
import LeanFormal.IUT.IUTI.InitialTheta.SourceClauseConstructors
import LeanFormal.IUT.IUTI.HodgeTheater.SourceDefinition31SignQuotientSupplyReduction

/-! # Stage-4 host: conditional SourceClauseConstructionWitness adapter for the model

Source anchors: IUT I, Definition 3.1 (initial Theta data, six-tuple with
clauses A--F over the arithmetic root and sign quotient); IUT I, Example 3.2,
(iv) (concrete Gaussian arithmetic).

CONSUMER: qpilot's from-scratch model skeleton (modelSourceDefinition31Data /
modelOriginalInput) needs a `SourceNativeInitialThetaData` for the Example 3.6
stage.  This file gives the CONDITIONAL adapter:
* LGPModelSourceClauseMissing l: the exact DATA still missing -- a concrete
  sign quotient over the concrete Gaussian arithmetic together with the clause
  assembly A--F (`SourceClauseAssembly`); these are data fields, not opaque
  propositions;
* lgpModelSourceClauseAssembly: given that data, build the theorem-level
  `SourceClauseConstructionWitness` via the existing
  `witnessOfClauseAssembly` (free fbar entry is canonical);
* lgpModelNativeData: given that data, build a concrete
  `SourceNativeInitialThetaData` via `SourceClauseConstructionWitness.sourceData`;
* lgpModelNativeData_of_witness: from any existing witness whose arithmetic is
  the concrete Gaussian arithmetic, get the native data with its arithmetic
  proof (subtype form, no dependent casts);
* arithmetic projection theorems for the skeleton.

LABEL: prerequisite component + exact missing data; NOT a paper object claim.
Registry frozen; new file only. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136ModelSourceClauseActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource

/-- The concrete Example 3.6 arithmetic root. -/
abbrev lgpModelArithmetic (l : PrimeGeFive) :
    InitialThetaArithmeticData l :=
  concreteGaussianInitialThetaArithmeticData l

/-- The EXACT missing model clause data: a concrete sign quotient over the
concrete Gaussian arithmetic plus the clause assembly A--F.  Data fields (not
opaque Props): an inhabitant would be the genuine concrete sign-quotient/clause
construction of IUT I, Definition 3.1. -/
structure LGPModelSourceClauseMissing (l : PrimeGeFive) where
  signQuotient : SourceSignQuotientData (lgpModelArithmetic l)
  assembly : SourceClauseAssembly (lgpModelArithmetic l) signQuotient

/-- Conditional construction of the theorem-level witness from the missing
exact data (canonical free fbar entry). -/
def lgpModelSourceClauseWitness
    (M : LGPModelSourceClauseMissing l) :
    SourceClauseConstructionWitness.{0} l :=
  witnessOfClauseAssembly (lgpModelArithmetic l) M.signQuotient M.assembly

/-- The conditional witness has the concrete Gaussian arithmetic. -/
theorem lgpModelSourceClauseWitness_arithmetic
    (M : LGPModelSourceClauseMissing l) :
    (lgpModelSourceClauseWitness M).arithmetic = lgpModelArithmetic l := rfl

/-- Conditional construction of the concrete native initial-Theta datum. -/
def lgpModelNativeData
    (M : LGPModelSourceClauseMissing l) :
    SourceNativeInitialThetaData.{0} l :=
  (lgpModelSourceClauseWitness M).sourceData

/-- The constructed native datum has the concrete Gaussian arithmetic. -/
theorem lgpModelNativeData_arithmetic
    (M : LGPModelSourceClauseMissing l) :
    (lgpModelNativeData M).arithmetic = lgpModelArithmetic l := rfl

/-- From any existing clause-construction witness with the concrete Gaussian
arithmetic, obtain the concrete native datum together with the arithmetic
proof (subtype form; no dependent casts needed). -/
def lgpModelNativeData_of_witness
    (W : SourceClauseConstructionWitness.{0} l)
    (h : W.arithmetic = lgpModelArithmetic l) :
    { D : SourceNativeInitialThetaData.{0} l //
        D.arithmetic = lgpModelArithmetic l } :=
  ⟨W.sourceData, by
    rw [SourceClauseConstructionWitness.sourceData_arithmetic]
    exact h⟩

#check lgpModelArithmetic
#check LGPModelSourceClauseMissing
#check lgpModelSourceClauseWitness
#check lgpModelSourceClauseWitness_arithmetic
#check lgpModelNativeData
#check lgpModelNativeData_arithmetic
#check lgpModelNativeData_of_witness

end LeanFormal.IUT.XiFPaper.S3136ModelSourceClauseActual
end