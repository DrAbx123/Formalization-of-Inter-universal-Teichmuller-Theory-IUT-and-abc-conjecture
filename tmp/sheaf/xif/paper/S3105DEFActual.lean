import tmp.sheaf.xif.paper.S2887CorrectedCoreMinimalActual
import tmp.sheaf.xif.paper.S2869A6CoreWithGenericQuotient
import tmp.sheaf.xif.paper.S3104ClausesCtoF
import tmp.sheaf.xif.paper.S2906CorrectedClauseABCD
import tmp.sheaf.xif.paper.S2907bClauseDEActual
import tmp.sheaf.xif.paper.S2907ClauseECorrected
import tmp.sheaf.xif.paper.S2907ClauseFCorrected
import tmp.sheaf.xif.paper.S2482CorrectedSourceSignQuotientActual
import tmp.sheaf.xif.paper.S2847A6ArithmeticActual
import tmp.sheaf.xif.paper.S2855A6CoreFromD6ConditionalActual
import tmp.sheaf.xif.paper.S2857StackAutoForA6Actual
import tmp.sheaf.xif.paper.S2858AlphaOverActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2887CorrectedCoreMinimalActual
open LeanFormal.IUT.XiFPaper.S2869A6CoreWithGenericQuotient
open LeanFormal.IUT.XiFPaper.S3104ClausesCtoF
open LeanFormal.IUT.XiFPaper.S2906CorrectedClauseABCD
open LeanFormal.IUT.XiFPaper.S2907bClauseDEActual
open LeanFormal.IUT.XiFPaper.S2907ClauseECorrected
open LeanFormal.IUT.XiFPaper.S2907ClauseFCorrected
open LeanFormal.IUT.XiFPaper.S2482CorrectedSourceSignQuotientActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual
open LeanFormal.IUT.XiFPaper.S2857StackAutoForA6Actual
open LeanFormal.IUT.XiFPaper.S2858AlphaOverActual
open CategoryTheory CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000
set_option relaxedAutoImplicit false

namespace LeanFormal.IUT.XiFPaper.S3105DEFActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-- The corrected S built by S2887Core from the actual core inputs. -/
noncomputable def S3105S
    (D : Pseudofunctor Iut.SignActionIndex
      (Iut.EtaleStackPseudofunctor S2847A6.F))
    (atBase : Bicategory.Equivalence (D.obj Iut.signActionObject)
      S2855HyperbolicOrbicurve.stack.fiber)
    (generator_identification :
      (atBase.inv ≫ D.map Iut.signActionGenerator) ≫ atBase.hom ≅
        S2857StackAuto alphaOverS2844)
    (I : S2887Inputs (S2869SignAction D atBase generator_identification)) :
    SourceSignQuotientDataCorrected S2847A6 :=
  S2887Core D atBase generator_identification I

/-- ClauseE selected data is actual from S: no extra input. -/
theorem S3105E_selected_eq_V
    (D : Pseudofunctor Iut.SignActionIndex
      (Iut.EtaleStackPseudofunctor S2847A6.F))
    (atBase : Bicategory.Equivalence (D.obj Iut.signActionObject)
      S2855HyperbolicOrbicurve.stack.fiber)
    (generator_identification :
      (atBase.inv ≫ D.map Iut.signActionGenerator) ≫ atBase.hom ≅
        S2857StackAuto alphaOverS2844)
    (I : S2887Inputs (S2869SignAction D atBase generator_identification)) :
    (S3105S D atBase generator_identification I).V =
      (S3105S D atBase generator_identification I).V_section.selected :=
  (S3105S D atBase generator_identification I).V_eq_section

/-- ClauseE selected equivalence is actual from S. -/
noncomputable def S3105E_selected_equiv
    (D : Pseudofunctor Iut.SignActionIndex
      (Iut.EtaleStackPseudofunctor S2847A6.F))
    (atBase : Bicategory.Equivalence (D.obj Iut.signActionObject)
      S2855HyperbolicOrbicurve.stack.fiber)
    (generator_identification :
      (atBase.inv ≫ D.map Iut.signActionGenerator) ≫ atBase.hom ≅
        S2857StackAuto alphaOverS2844)
    (I : S2887Inputs (S2869SignAction D atBase generator_identification)) :
    NumberFieldPlace S2847A6.Fmod ≃
      {v : NumberFieldPlace S2847A6.K //
        v ∈ (S3105S D atBase generator_identification I).V} :=
  (S3105S D atBase generator_identification I).V_mod_bijection

/-- Missing fields of ClauseD/E/F not present in S2887Inputs. -/
structure S3105DEFMissing : Type where
  clauseD_missing : List String
  clauseE_missing : List String
  clauseF_missing : List String

/-- The exact missing lists. -/
noncomputable def S3105DEFMissingData : S3105DEFMissing where
  clauseD_missing :=
    [ "kSignAction : OrbicurveSignAction S.xK"
    , "kQuotient : OrbicurveSignInvariantMorphism kSignAction S.cK"
    , "kQuotientWitness : OrbicurveSignQuotientWitness kSignAction kQuotient"
    , "kQuotientExtension : SourceOrbicurveMorphismScalarExtension S.xKExtension S.cKExtension S.quotient.map"
    , "kQuotientMapEqExtension : kQuotient.map = cast ... kQuotientExtension.result"
    , "kTorsionCover : SourceOrbicurveFiniteEtaleCover S.xK S.cK"
    , "kTorsionCoverMapEqQuotient : kTorsionCover.map = kQuotient.map"
    , "xGroups : SourceOrbicurveGroupData S.xK (AbsoluteGaloisProfinite A.K)"
    , "cGroups : SourceOrbicurveGroupData S.cK (AbsoluteGaloisProfinite A.K)"
    , "groupInclusion : ProfiniteFundamentalGroupInclusion ..."
    , "xToFGroups : ProfiniteFundamentalExactSequenceEmbedding ..."
    , "cToFGroups : ProfiniteFundamentalExactSequenceEmbedding ..." ]
  clauseE_missing :=
    [ "finiteLocal : forall selected finite v, S2907FiniteLocalSourceCorrected ..."
    , "infiniteLocal : forall selected infinite v, S2907InfiniteLocalSourceCorrected ..." ]
  clauseF_missing :=
    [ "originMap : {q : canonicalKQuotient.Quotient // q != 0} -> OrbicurveBoundaryCusp S.cK"
    , "originMap_epsilon : originMap distinguishedClass = S.epsilon"
    , "cuspDecomposition : OrbicurveCuspidalDecompositionData E.c_groups.groups"
    , "cuspDecomposition_origin : cuspDecomposition.cusp = BoundaryOrigin.cusp" ]

#check S3105S
#check S3105E_selected_eq_V
#check S3105E_selected_equiv
#check S3105DEFMissingData
#print axioms S3105S
#print axioms S3105E_selected_eq_V
#print axioms S3105E_selected_equiv

end LeanFormal.IUT.XiFPaper.S3105DEFActual
end