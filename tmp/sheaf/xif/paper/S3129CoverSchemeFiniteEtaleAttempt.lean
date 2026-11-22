import tmp.sheaf.xif.paper.S3127CoverMorphismActual
import tmp.sheaf.xif.paper.S3128PullbackCoproductActual
import tmp.sheaf.xif.paper.S3129RepresentableFiniteEtaleActual

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.RepresentableCoverChosenCategoryActual
open LeanFormal.IUT.XiFPaper.S3127CoverMorphismActual
open LeanFormal.IUT.XiFPaper.S3128PullbackCoproductActual
open LeanFormal.IUT.XiFPaper.S3129RepresentableFiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S3129CoverSchemeFiniteEtaleActual

variable {l : PrimeGeFive}

/-- The identity point of the terminal target stack. -/
noncomputable def S3129IdentityPoint :
    Pseudofunctor.StrongTrans
      (S1742YS (F := S1348K l) (S1419AffineOver (l := l)))
      (S1536XF (l := l)).stack.fiber :=
  Pseudofunctor.StrongTrans.id (S1742YS (F := S1348K l) (S1419AffineOver (l := l)))

/-- The scheme-level finite-etale certificate of a chosen-scheme cover. -/
def S3129CoverSchemeFiniteEtaleTarget (A : S3127Cover (l := l)) : Prop :=
  AlgebraicGeometry.IsFinite (S3128ToSchemeMap A).left ∧
    AlgebraicGeometry.Etale (S3128ToSchemeMap A).left

/-- The scheme-level certificate is exactly the structure field. -/
theorem S3129CoverSchemeFiniteEtale (A : S3127Cover (l := l)) :
    S3129CoverSchemeFiniteEtaleTarget (l := l) A :=
  A.finiteEtale

/-- Scheme-level certificate derives the stack-level finite-etale certificate. -/
noncomputable def S3129CoverStackFiniteEtale (A : S3127Cover (l := l)) :
    EtaleStackFiniteEtaleMorphism A.map :=
  (S3127ToOrbicurveCover (l := l) A).finiteEtale

#check S3129IdentityPoint
#check S3129CoverSchemeFiniteEtaleTarget
#check S3129CoverSchemeFiniteEtale
#check S3129CoverStackFiniteEtale

end LeanFormal.IUT.XiFPaper.S3129CoverSchemeFiniteEtaleActual
end