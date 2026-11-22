import tmp.sheaf.xif.paper.S2817ClauseDEFScaffold
import LeanFormal.IUT.IUTI.HodgeTheater.SourceClauseAssemblyUnitsReduction

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2817ClauseDEFScaffold
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2823ClauseDConditionalActual

universe u
variable {l : PrimeGeFive}
variable {A : InitialThetaArithmeticData.{u} l}
variable {S : SourceSignQuotientData A}
variable {C : SourceClauseA A S}
variable {B : SourceClauseB A S C}
variable {D : SourceClauseC A S C B}
variable {E : SourceClauseD A S C B D}
variable {L : SourceClauseE A S C B D E}

/-- Conditional ClauseD: the 11 K-side/group witnesses are explicit. -/
noncomputable def S2823ClauseD
    (W : S2817ClauseDScaffold (l := l) (A := A) (S := S)) :
    SourceClauseD A S C B D :=
  S2817ClauseD W

/-- Conditional ClauseE via the local-family unit supplier. -/
noncomputable def S2823ClauseE
    (U : SourceClauseELocalFamilyUnit A S C B D E) :
    SourceClauseE A S C B D E :=
  SourceClauseELocalFamilyUnit.assemble U

/-- Conditional ClauseF via the boundary unit supplier. -/
noncomputable def S2823ClauseF
    (U : SourceClauseFBoundaryUnit A S C B D E L) :
    SourceClauseF A S C B D E L :=
  SourceClauseFBoundaryUnit.assemble U

/-- Bundled conditional D/E/F data: K-side witnesses + local-family unit +
boundary unit. -/
structure S2823ClauseDEFData where
  kSide : S2817ClauseDScaffold (l := l) (A := A) (S := S)
  localFamily : SourceClauseELocalFamilyUnit A S C B D
    (S2817ClauseD kSide)
  boundary : SourceClauseFBoundaryUnit A S C B D
    (S2817ClauseD kSide)
    (SourceClauseELocalFamilyUnit.assemble localFamily)

/-- ClauseD from the bundled data. -/
noncomputable def S2823ClauseDEFData.clauseD
    (W : S2823ClauseDEFData (l := l) (A := A) (S := S)
      (C := C) (B := B) (D := D)) :
    SourceClauseD A S C B D :=
  S2817ClauseD W.kSide

/-- ClauseE from the bundled data. -/
noncomputable def S2823ClauseDEFData.clauseE
    (W : S2823ClauseDEFData (l := l) (A := A) (S := S)
      (C := C) (B := B) (D := D)) :
    SourceClauseE A S C B D W.clauseD :=
  SourceClauseELocalFamilyUnit.assemble W.localFamily

/-- ClauseF from the bundled data. -/
noncomputable def S2823ClauseDEFData.clauseF
    (W : S2823ClauseDEFData (l := l) (A := A) (S := S)
      (C := C) (B := B) (D := D)) :
    SourceClauseF A S C B D W.clauseD W.clauseE :=
  SourceClauseFBoundaryUnit.assemble W.boundary

#check S2823ClauseD
#check S2823ClauseE
#check S2823ClauseF
#check S2823ClauseDEFData
#check S2823ClauseDEFData.clauseD
#check S2823ClauseDEFData.clauseE
#check S2823ClauseDEFData.clauseF
#print axioms S2823ClauseDEFData.clauseD
#print axioms S2823ClauseDEFData.clauseE
#print axioms S2823ClauseDEFData.clauseF

end LeanFormal.IUT.XiFPaper.S2823ClauseDConditionalActual
end
