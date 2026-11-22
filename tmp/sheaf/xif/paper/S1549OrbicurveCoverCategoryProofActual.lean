import tmp.sheaf.xif.paper.S1522OrbicurveEtalePiActual
import Iut.Foundations.Orbicurve

-- S1549: the coverCategory obstruction is not only id/comp coherence.
-- The field is Category.{0,1} (OrbicurveFiniteEtaleCover X), whose Hom
-- family must live in Type 0, while the actual over-map type
-- OrbicurveFiniteEtaleCoverMap lives in Type 1.  The exact first missing
-- structure is a small Hom carrier with an equivalence to the actual
-- over-maps, together with the Category structure on it.
-- No group product/l-torsion/terminal substitute.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1549OrbicurveCoverCategoryProofActual

open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1522OrbicurveEtalePiActual
open LeanFormal.IUT.XiFPaper.S1319OrbicurveClauseActual

variable {l : PrimeGeFive}

noncomputable abbrev S1549Orbicurve : Iut.HyperbolicOrbicurve (S1348K l) :=
  S1522Orbicurve l

abbrev S1549Cover : Type 1 :=
  Iut.OrbicurveFiniteEtaleCover (S1549Orbicurve (l := l))

abbrev S1549CoverMap (A B : S1549Cover (l := l)) : Type 1 :=
  Iut.OrbicurveFiniteEtaleCoverMap A B

/-- Exact first missing structural data: a small (Type 0) Hom carrier with
an equivalence to the actual over-map type. -/
structure S1549SmallHomFirstMissing where
  Hom : S1549Cover (l := l) → S1549Cover (l := l) → Type
  homEquiv : ∀ A B : S1549Cover (l := l), Hom A B ≃ S1549CoverMap A B

/-- The full exact first missing field: a Category.{0,1} on the cover type. -/
def S1549CoverCategoryFirstMissing : Type 1 :=
  Category.{0, 1} (S1549Cover (l := l))

def S1549CoverCategoryRequired : Type 1 := S1549CoverCategoryFirstMissing (l := l)

def S1549SmallHomRequired : Type 1 := S1549SmallHomFirstMissing (l := l)

/-- Actual non-group prefix: the S1419 orbicurve is nonterminal with the
once-punctured signature. -/
theorem S1549Orbicurve_signature :
    (S1549Orbicurve (l := l)).signature =
      Iut.OrbicurveSignature.oncePuncturedElliptic :=
  S1522Orbicurve_signature l

theorem S1549Orbicurve_nonterminal :
    S1319NonterminalFiber (S1549Orbicurve (l := l)) :=
  S1522Orbicurve_nonterminal l

#check S1549Cover
#check S1549CoverMap
#check S1549SmallHomFirstMissing
#check S1549CoverCategoryFirstMissing
#check S1549SmallHomRequired
#check S1549CoverCategoryRequired
#check S1549Orbicurve_signature
#check S1549Orbicurve_nonterminal

end LeanFormal.IUT.XiFPaper.S1549OrbicurveCoverCategoryProofActual

end