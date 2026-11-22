import tmp.sheaf.xif.paper.S1566SmallHomCoverCategoryActual
import tmp.sheaf.xif.paper.S405OrbicurveCoverCategoryActual

-- S1568: exact small-skeleton first missing for the Type 0 cover category.
-- A Type 0 Skeleton with an equivalence to covers, a Category.{0,0} on it,
-- and a hom equivalence to the actual Type 1 cover maps.  No Shrink/ULift.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1568CoverSkeletonActual

open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1522OrbicurveEtalePiActual
open LeanFormal.IUT.XiFPaper.S1319OrbicurveClauseActual
open LeanFormal.IUT.XiFPaper.S1562CoverCategoryUniverseActual
open LeanFormal.IUT.XiFPaper.S1566SmallHomCoverCategoryActual

variable {l : PrimeGeFive}

abbrev S1568Cover : Type 1 := S1566Cover (l := l)

abbrev S1568CoverMap (A B : S1568Cover (l := l)) : Type 1 :=
  S1566CoverMap (l := l) A B

/-- Actual identity map on every cover, reused from S405. -/
noncomputable def S1568Id (A : S1568Cover (l := l)) :
    S1568CoverMap (l := l) A A :=
  LeanFormal.IUT.XiFPaper.S405OrbicurveCoverCategoryActual.OrbicurveFiniteEtaleCover.idMap
    (X := S1562Orbicurve (l := l)) A

/-- Exact small-skeleton first missing. -/
structure S1568SmallSkeleton where
  Skeleton : Type
  objEquiv : Skeleton ≃ S1568Cover (l := l)
  coverCategory : Category.{0, 0} Skeleton
  homEquiv : ∀ a b : Skeleton,
    @Quiver.Hom _ coverCategory.toQuiver a b ≃
      S1568CoverMap (l := l) (objEquiv a) (objEquiv b)

/-- Exact composition data still missing independently of the skeleton. -/
def S1568CompositionRequired : Type 1 :=
  ∀ (A B C : S1568Cover (l := l))
    (f : S1568CoverMap (l := l) A B)
    (g : S1568CoverMap (l := l) B C),
    S1568CoverMap (l := l) A C

def S1568SmallSkeletonRequired : Type 1 :=
  @S1568SmallSkeleton l

/-- The original Type 0 hom category remains the exact missing target. -/
def S1568OriginalCategoryRequired : Type 1 :=
  Category.{0, 1} (S1568Cover (l := l))

/-- Actual non-group prefix. -/
theorem S1568Orbicurve_signature :
    (S1562Orbicurve (l := l)).signature =
      Iut.OrbicurveSignature.oncePuncturedElliptic :=
  S1522Orbicurve_signature l

theorem S1568Orbicurve_nonterminal :
    S1319NonterminalFiber (S1562Orbicurve (l := l)) :=
  S1522Orbicurve_nonterminal l

#check S1568Id
#check S1568SmallSkeleton
#check S1568CompositionRequired
#check S1568SmallSkeletonRequired
#check S1568OriginalCategoryRequired
#check S1568Orbicurve_signature
#check S1568Orbicurve_nonterminal

end LeanFormal.IUT.XiFPaper.S1568CoverSkeletonActual

end