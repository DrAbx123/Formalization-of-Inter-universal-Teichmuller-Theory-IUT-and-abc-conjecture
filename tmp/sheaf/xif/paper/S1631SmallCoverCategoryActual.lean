import tmp.sheaf.xif.paper.S1568CoverSkeletonActual

-- S1631: small cover category / skeleton remains the exact first missing.
-- No Shrink/ULift/arbitrary small carrier is used.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1631SmallCoverCategoryActual

open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1522OrbicurveEtalePiActual
open LeanFormal.IUT.XiFPaper.S1319OrbicurveClauseActual
open LeanFormal.IUT.XiFPaper.S1562CoverCategoryUniverseActual
open LeanFormal.IUT.XiFPaper.S1566SmallHomCoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1568CoverSkeletonActual

variable {l : PrimeGeFive}

abbrev S1631Cover : Type 1 := S1566Cover (l := l)

abbrev S1631CoverMap (A B : S1631Cover (l := l)) : Type 1 :=
  S1566CoverMap (l := l) A B

/-- Exact small cover category/skeleton first missing data. -/
structure S1631SmallCoverCategory where
  Skeleton : Type
  objEquiv : Skeleton ≃ S1631Cover (l := l)
  category : Category.{0, 0} Skeleton
  homEquiv : ∀ a b : Skeleton,
    @Quiver.Hom _ category.toQuiver a b ≃
      S1631CoverMap (l := l) (objEquiv a) (objEquiv b)

/-- Any original Category.{0,1} supplies a Type 0 Hom carrier. -/
def S1631HomCarrierOfCategory (C : Category.{0, 1} (S1631Cover (l := l))) :
    S1631Cover (l := l) → S1631Cover (l := l) → Type :=
  C.Hom

/-- Exact missing composition data on actual cover maps. -/
def S1631CompositionRequired : Type 1 :=
  ∀ (A B C : S1631Cover (l := l))
    (f : S1631CoverMap (l := l) A B)
    (g : S1631CoverMap (l := l) B C),
    S1631CoverMap (l := l) A C

def S1631OriginalCategoryRequired : Type 1 :=
  Category.{0, 1} (S1631Cover (l := l))

def S1631SmallCoverCategoryRequired : Type 1 :=
  @S1631SmallCoverCategory l

/-- Actual identity map on covers, reused from S405. -/
noncomputable def S1631Id (A : S1631Cover (l := l)) :
    S1631CoverMap (l := l) A A :=
  S1568Id (l := l) A

theorem S1631Orbicurve_signature :
    (S1562Orbicurve (l := l)).signature =
      Iut.OrbicurveSignature.oncePuncturedElliptic :=
  S1522Orbicurve_signature l

theorem S1631Orbicurve_nonterminal :
    S1319NonterminalFiber (S1562Orbicurve (l := l)) :=
  S1522Orbicurve_nonterminal l

#check S1631Cover
#check S1631CoverMap
#check S1631SmallCoverCategory
#check S1631HomCarrierOfCategory
#check S1631CompositionRequired
#check S1631OriginalCategoryRequired
#check S1631SmallCoverCategoryRequired
#check S1631Id
#check S1631Orbicurve_signature
#check S1631Orbicurve_nonterminal

end LeanFormal.IUT.XiFPaper.S1631SmallCoverCategoryActual

end