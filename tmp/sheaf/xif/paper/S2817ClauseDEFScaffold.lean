import tmp.sheaf.xif.paper.S2816ClauseACReadyActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceClauseConstructors

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2817ClauseDEFScaffold

universe u

variable {l : PrimeGeFive}
variable {A : InitialThetaArithmeticData.{u} l}
variable {S : SourceSignQuotientData A}
variable {C : SourceClauseA A S}
variable {B : SourceClauseB A S C}
variable {D : SourceClauseC A S C B}

/-- Conditional data for ClauseD. All fields are the literal K-side witnesses
of SourceClauseD.ofKSideWitnesses. -/
structure S2817ClauseDScaffold where
  kSignAction : Iut.OrbicurveSignAction S.xK
  kQuotient : Iut.OrbicurveSignInvariantMorphism kSignAction S.cK
  kQuotientWitness : Iut.OrbicurveSignQuotientWitness kSignAction kQuotient
  kQuotientExtension : SourceOrbicurveMorphismScalarExtension
    S.xKExtension S.cKExtension S.quotient.map
  kQuotientMapEqExtension : kQuotient.map = Iut.HyperbolicOrbicurve.Hom.cast
    S.xK_eq_extension.symm S.cK_eq_extension.symm kQuotientExtension.result
  kTorsionCover : SourceOrbicurveFiniteEtaleCover S.xK S.cK
  kTorsionCoverMapEqQuotient : kTorsionCover.map = kQuotient.map
  xGroups : SourceOrbicurveGroupData S.xK
    (Iut.AbsoluteGaloisProfinite A.K)
  cGroups : SourceOrbicurveGroupData S.cK
    (Iut.AbsoluteGaloisProfinite A.K)
  groupInclusion :
    Iut.ProfiniteFundamentalGroupInclusion
      xGroups.sequence.geometric xGroups.sequence.arithmetic
      cGroups.sequence.geometric cGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite A.K) xGroups.sequence cGroups.sequence
  xToFGroups :
    Iut.ProfiniteFundamentalExactSequenceEmbedding
      xGroups.sequence.geometric xGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite A.K)
      S.xFGroups.sequence.geometric S.xFGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite A.F) xGroups.sequence S.xFGroups.sequence
  cToFGroups :
    Iut.ProfiniteFundamentalExactSequenceEmbedding
      cGroups.sequence.geometric cGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite A.K)
      S.cFGroups.sequence.geometric S.cFGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite A.F) cGroups.sequence S.cFGroups.sequence

/-- Actual ClauseD from the scaffold: the constructor is used literally. -/
noncomputable def S2817ClauseD (W : S2817ClauseDScaffold
    (l := l) (A := A) (S := S)) :
    SourceClauseD A S C B D :=
  SourceClauseD.ofKSideWitnesses W.kSignAction W.kQuotient
    W.kQuotientWitness W.kQuotientExtension W.kQuotientMapEqExtension
    W.kTorsionCover W.kTorsionCoverMapEqQuotient W.xGroups W.cGroups
    W.groupInclusion W.xToFGroups W.cToFGroups

variable {E : SourceClauseD A S C B D}

/-- Conditional data for ClauseE: exactly the completion-level local families. -/
structure S2817ClauseEScaffold where
  finiteLocal : ∀ (v : {v : NumberFieldPlace A.K // v ∈ S.V})
    (hv : v.1.IsFinite),
    SourceFiniteLocalSource A S C B D E (selectedFinitePlace hv)
  infiniteLocal : ∀ (v : {v : NumberFieldPlace A.K // v ∈ S.V})
    (hv : v.1.IsInfinite),
    SourceInfiniteLocalSource A S C B D E (selectedInfinitePlace hv)

/-- Actual ClauseE from the local-family scaffold. -/
noncomputable def S2817ClauseE (W : S2817ClauseEScaffold
    (l := l) (A := A) (S := S) (C := C) (B := B) (D := D) (E := E)) :
    SourceClauseE A S C B D E :=
  SourceClauseE.ofLocalFamilies W.finiteLocal W.infiniteLocal

variable {L : SourceClauseE A S C B D E}

/-- Conditional data for ClauseF: origin map, distinguished-cusp equation and
cusp decomposition. -/
structure S2817ClauseFScaffold where
  originMap :
    {q : (SourceClauseF.canonicalKQuotientData C B D).Quotient // q ≠ 0}
      → Iut.OrbicurveBoundaryCusp S.cK
  originMap_epsilon :
    originMap
      ⟨(SourceClauseF.canonicalKQuotientData C B D).distinguishedClass,
        (SourceClauseF.canonicalKQuotientData C B D).distinguishedClass_nonzero⟩
      = S.epsilon
  cuspDecomposition : Iut.OrbicurveCuspidalDecompositionData E.c_groups.groups
  cuspDecomposition_origin :
    cuspDecomposition.cusp =
      (SourceClauseF.ofCanonicalKBoundaryOrigin C B D
        originMap originMap_epsilon).cusp

/-- Actual ClauseF from the boundary/cusp scaffold. -/
noncomputable def S2817ClauseF (W : S2817ClauseFScaffold
    (l := l) (A := A) (S := S) (C := C) (B := B) (D := D) (E := E)) :
    SourceClauseF A S C B D E L :=
  SourceClauseF.ofCanonicalBoundaryData C B D E L W.originMap
    W.originMap_epsilon W.cuspDecomposition W.cuspDecomposition_origin

#check S2817ClauseDScaffold
#check S2817ClauseD
#check S2817ClauseEScaffold
#check S2817ClauseE
#check S2817ClauseFScaffold
#check S2817ClauseF
#print axioms S2817ClauseD
#print axioms S2817ClauseE
#print axioms S2817ClauseF

end LeanFormal.IUT.XiFPaper.S2817ClauseDEFScaffold
end
