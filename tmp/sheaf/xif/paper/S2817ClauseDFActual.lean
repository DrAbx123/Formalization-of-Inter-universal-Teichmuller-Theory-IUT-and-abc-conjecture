import tmp.sheaf.xif.paper.S2817ClauseDEFScaffold
import tmp.sheaf.xif.paper.S1376PaperKCoreRestatementActual
import tmp.sheaf.xif.paper.S2823ClauseDConditionalActual
import LeanFormal.IUT.IUTI.HodgeTheater.SourceClauseAssemblyUnitsReduction
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2817ClauseDEFScaffold
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1376PaperKCoreRestatementActual
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000
namespace LeanFormal.IUT.XiFPaper.S2817ClauseDFActual
universe u

/-- Extract the 11 K-side witnesses of ClauseD scaffold from an actual
SourceClauseD. -/
noncomputable def S2817ClauseDScaffold_ofSourceClauseD
    {l : PrimeGeFive} {A : InitialThetaArithmeticData.{u} l}
    {S : SourceSignQuotientData A} {C : SourceClauseA A S}
    {B : SourceClauseB A S C} {D : SourceClauseC A S C B}
    (E : SourceClauseD A S C B D) :
    S2817ClauseDScaffold (l := l) (A := A) (S := S) where
  kSignAction := E.k_signAction
  kQuotient := E.k_quotient
  kQuotientWitness := E.k_quotientWitness
  kQuotientExtension := E.k_quotientExtension
  kQuotientMapEqExtension := E.k_quotient_map_eq_extension
  kTorsionCover := E.k_l_torsion_cover
  kTorsionCoverMapEqQuotient := E.k_l_torsion_cover_map_eq_quotient
  xGroups := E.x_groups
  cGroups := E.c_groups
  groupInclusion := E.group_inclusion
  xToFGroups := E.x_to_F_groups
  cToFGroups := E.c_to_F_groups

/-- From a paper clause D record plus the two scalar-extension fields, obtain
the 11-field K-side scaffold actual. -/
noncomputable def S2817ClauseDScaffold_ofPaper
    {l : PrimeGeFive} {S : SourceSignQuotientData (S1280Arithmetic l)}
    {C : SourceClauseA (S1280Arithmetic l) S}
    {B : SourceClauseB (S1280Arithmetic l) S C}
    {D : SourceClauseC (S1280Arithmetic l) S C B}
    (P : S1376PaperClauseD S C B D)
    (kQuotientExtension : SourceOrbicurveMorphismScalarExtension
      S.xKExtension S.cKExtension S.quotient.map)
    (kQuotientMapEqExtension :
      P.k_quotient.map = Iut.HyperbolicOrbicurve.Hom.cast
        S.xK_eq_extension.symm S.cK_eq_extension.symm
        kQuotientExtension.result) :
    S2817ClauseDScaffold (l := l) (A := S1280Arithmetic l) (S := S) :=
  S2817ClauseDScaffold_ofSourceClauseD
    (S1376PaperClauseD.toSourceClauseD P kQuotientExtension
      kQuotientMapEqExtension)

/-- Boundary 4-field scaffold from the actual SourceClauseFBoundaryUnit. -/
noncomputable def S2817ClauseFScaffold_ofBoundaryUnit
    {l : PrimeGeFive} {A : InitialThetaArithmeticData.{u} l}
    {S : SourceSignQuotientData A} {C : SourceClauseA A S}
    {B : SourceClauseB A S C} {D : SourceClauseC A S C B}
    {K : SourceClauseD A S C B D} {L : SourceClauseE A S C B D K}
    (U : SourceClauseFBoundaryUnit A S C B D K L) :
    S2817ClauseFScaffold (l := l) (A := A) (S := S)
      (C := C) (B := B) (D := D) (E := K) where
  originMap := U.originMap
  originMap_epsilon := U.originMap_epsilon
  cuspDecomposition := U.cuspDecomposition
  cuspDecomposition_origin := U.cuspDecomposition_cusp_eq_origin

#check S2817ClauseDScaffold_ofSourceClauseD
#check S2817ClauseDScaffold_ofPaper
#check S2817ClauseFScaffold_ofBoundaryUnit
#print axioms S2817ClauseDScaffold_ofSourceClauseD
#print axioms S2817ClauseDScaffold_ofPaper
#print axioms S2817ClauseFScaffold_ofBoundaryUnit

end LeanFormal.IUT.XiFPaper.S2817ClauseDFActual