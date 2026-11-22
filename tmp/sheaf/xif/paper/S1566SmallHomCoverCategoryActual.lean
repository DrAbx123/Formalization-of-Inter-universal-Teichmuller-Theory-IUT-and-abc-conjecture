import tmp.sheaf.xif.paper.S1562CoverCategoryUniverseActual

-- S1566: no small Type 0 Hom carrier is constructed from the actual
-- Type 1 over-map type without Shrink/ULift.  The faithful correction is
-- the universe-matched interface Category.{1,1}; both are exact fields.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1566SmallHomCoverCategoryActual

open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1522OrbicurveEtalePiActual
open LeanFormal.IUT.XiFPaper.S1319OrbicurveClauseActual
open LeanFormal.IUT.XiFPaper.S1562CoverCategoryUniverseActual

variable {l : PrimeGeFive}

abbrev S1566Cover : Type 1 := S1562Cover (l := l)

abbrev S1566CoverMap (A B : S1566Cover (l := l)) : Type 1 :=
  S1562CoverMap (l := l) A B

/-- Exact small-Hom requirement.  There is no inhabitant: the actual
cover-map type is Type 1, so this is an additional small carrier
equivalence, not a definitional identity. -/
structure S1566SmallHomData where
  Hom : S1566Cover (l := l) → S1566Cover (l := l) → Type
  homEquiv : ∀ A B : S1566Cover (l := l), Hom A B ≃ S1566CoverMap A B

/-- The corrected faithful interface at the matching universe. -/
structure S1566CorrectedFirstFields where
  coverCategory : Category.{1, 1} (S1566Cover (l := l))
  galoisCategory :
    letI := coverCategory;
    @GaloisCategory.{1, 1} (S1566Cover (l := l)) coverCategory

/-- Original small-hom interface, retained exactly. -/
def S1566OriginalCategoryRequired : Type 1 :=
  Category.{0, 1} (S1566Cover (l := l))

/-- Corrected universe interface, retained exactly. -/
def S1566CorrectedCategoryRequired : Type 2 :=
  Category.{1, 1} (S1566Cover (l := l))

def S1566SmallHomRequired : Type 1 := S1566SmallHomData (l := l)

def S1566CorrectedFirstFieldsRequired : Type 2 :=
  S1566CorrectedFirstFields (l := l)

/-- Actual non-group prefix. -/
theorem S1566Orbicurve_signature :
    (S1562Orbicurve (l := l)).signature =
      Iut.OrbicurveSignature.oncePuncturedElliptic :=
  S1522Orbicurve_signature l

theorem S1566Orbicurve_nonterminal :
    S1319NonterminalFiber (S1562Orbicurve (l := l)) :=
  S1522Orbicurve_nonterminal l

#check S1566CoverMap
#check S1566SmallHomData
#check S1566CorrectedFirstFields
#check S1566OriginalCategoryRequired
#check S1566CorrectedCategoryRequired
#check S1566SmallHomRequired
#check S1566CorrectedFirstFieldsRequired
#check S1566Orbicurve_signature
#check S1566Orbicurve_nonterminal

end LeanFormal.IUT.XiFPaper.S1566SmallHomCoverCategoryActual

end