import Iut.Foundations.Orbicurve
import tmp.sheaf.xif.paper.S1522OrbicurveEtalePiActual

-- S1562: universe audit of coverCategory.
-- Local Iut/Foundations/Orbicurve.lean and both vendored promachina
-- snapshots have exactly: coverCategory : Category.{u} (Cover X), F : Type u.
-- So the local structure is not a port-universe error.  For F = S1348K l
-- (Type 0), u = 0, hence Category.{0,1} (objects Type 1, homs Type 0) is
-- the field forced by the original interface, not an S1522/S1529 typo.
-- Actual OrbicurveFiniteEtaleCoverMap is Type 1, so it cannot be the Hom
-- of that original field; a small Hom carrier or a corrected interface is
-- required.  No Shrink/ULift carrier and no fake Category is inserted.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1562CoverCategoryUniverseActual

open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1522OrbicurveEtalePiActual
open LeanFormal.IUT.XiFPaper.S1319OrbicurveClauseActual

variable {l : PrimeGeFive}

noncomputable abbrev S1562Orbicurve : Iut.HyperbolicOrbicurve (S1348K l) :=
  S1522Orbicurve l

abbrev S1562Cover : Type 1 :=
  Iut.OrbicurveFiniteEtaleCover (S1562Orbicurve (l := l))

abbrev S1562CoverMap (A B : S1562Cover (l := l)) : Type 1 :=
  Iut.OrbicurveFiniteEtaleCoverMap A B

/-- The original interface field, specialized to the S1348 Gaussian field:
objects Type 1, homs Type 0.  This is forced by Iut.coverCategory. -/
def S1562OriginalCoverCategory : Type 1 :=
  Category.{0, 1} (S1562Cover (l := l))

/-- The corrected universe interface: objects Type 1, homs Type 1, matching
the actual cover-map type.  This does NOT fill the original
OrbicurveEtaleFundamentalGroup.coverCategory field; it is the proposed
corrected field type. -/
def S1562CorrectedCoverCategory : Type 2 :=
  Category.{1, 1} (S1562Cover (l := l))

/-- Corrected GaloisCategory field type at the matching universe. -/
def S1562CorrectedGaloisCategory
    (C : S1562CorrectedCoverCategory (l := l)) : Prop :=
  @GaloisCategory.{1, 1} (S1562Cover (l := l)) C

/-- Under the original interface, any Category has a Type 0 Hom carrier. -/
def S1562OriginalHomCarrier (C : S1562OriginalCoverCategory (l := l)) :
    S1562Cover (l := l) → S1562Cover (l := l) → Type :=
  C.Hom

/-- The S1549 small Hom carrier condition; no inhabitant is asserted. -/
structure S1562OriginalSmallHomFirstMissing where
  Hom : S1562Cover (l := l) → S1562Cover (l := l) → Type
  homEquiv : ∀ A B : S1562Cover (l := l), Hom A B ≃ S1562CoverMap A B

/-- Exact first missing for the corrected universe interface. -/
def S1562CorrectedCategoryRequired : Type 2 :=
  S1562CorrectedCoverCategory (l := l)

def S1562OriginalCategoryRequired : Type 1 :=
  S1562OriginalCoverCategory (l := l)

def S1562SmallHomRequired : Type 1 :=
  S1562OriginalSmallHomFirstMissing (l := l)

theorem S1562Orbicurve_signature :
    (S1562Orbicurve (l := l)).signature =
      Iut.OrbicurveSignature.oncePuncturedElliptic :=
  S1522Orbicurve_signature l

theorem S1562Orbicurve_nonterminal :
    S1319NonterminalFiber (S1562Orbicurve (l := l)) :=
  S1522Orbicurve_nonterminal l

#check Iut.OrbicurveEtaleFundamentalGroup
#check S1562Cover
#check S1562CoverMap
#check S1562OriginalCoverCategory
#check S1562CorrectedCoverCategory
#check S1562CorrectedGaloisCategory
#check S1562OriginalHomCarrier
#check S1562OriginalSmallHomFirstMissing
#check S1562CorrectedCategoryRequired
#check S1562OriginalCategoryRequired
#check S1562Orbicurve_signature
#check S1562Orbicurve_nonterminal

end LeanFormal.IUT.XiFPaper.S1562CoverCategoryUniverseActual

end