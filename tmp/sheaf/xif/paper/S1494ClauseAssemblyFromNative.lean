import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import LeanFormal.IUT.IUTI.HodgeTheater.SourceDefinition31SignQuotientSupplyReduction

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 400000

namespace LeanFormal.IUT.XiFPaper.S1494ClauseAssemblyFromNative

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource

universe u

/-- Conditional actual assembly: a native initial Theta datum already carries
all six clauses, hence its own `SourceClauseAssembly`. -/
def sourceClauseAssemblyOfNative
    {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{u} l) :
    SourceClauseAssembly T.arithmetic T.tuple.source where
  clauseA := T.clauseA
  clauseB := T.clauseB
  clauseC := T.clauseC
  clauseD := T.clauseD
  clauseE := T.clauseE
  clauseF := T.clauseF

/-- Conditional nonempty assembly from a native root. -/
theorem sourceClauseAssembly_nonempty_of_native
    {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{u} l) :
    Nonempty (SourceClauseAssembly T.arithmetic T.tuple.source) :=
  ⟨sourceClauseAssemblyOfNative T⟩

/-- The exact remaining input for a paper arithmetic root A. -/
abbrev NativeRootOf {l : PrimeGeFive} (A : InitialThetaArithmeticData.{u} l) :=
  { T : SourceNativeInitialThetaData.{u} l // T.arithmetic = A }

theorem exists_sourceClauseAssembly_of_nativeRoot
    {l : PrimeGeFive} {A : InitialThetaArithmeticData.{u} l}
    (R : NativeRootOf A) :
    ∃ SQ : SourceSignQuotientData A,
      Nonempty (SourceClauseAssembly A SQ) := by
  obtain ⟨T, rfl⟩ := R
  exact ⟨T.tuple.source, sourceClauseAssembly_nonempty_of_native T⟩

#check sourceClauseAssemblyOfNative
#check sourceClauseAssembly_nonempty_of_native
#check exists_sourceClauseAssembly_of_nativeRoot
#print axioms sourceClauseAssemblyOfNative
#print axioms exists_sourceClauseAssembly_of_nativeRoot

end LeanFormal.IUT.XiFPaper.S1494ClauseAssemblyFromNative
end
