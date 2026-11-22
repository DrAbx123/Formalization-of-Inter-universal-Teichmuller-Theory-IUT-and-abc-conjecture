import tmp.sheaf.xif.paper.S1529OrbicurveGaloisCategoryActual

-- S1538: the cover category remains the exact first missing field.
-- The actual cover type and its over-map object structure are present; a
-- Category instance would require the identity/composition 2-cell coherence
-- of OrbicurveFiniteEtaleCoverMap, which the tree does not supply.
-- No group product/l-torsion/terminal substitute.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1538OrbicurveCoverCategoryActual

open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1522OrbicurveEtalePiActual
open LeanFormal.IUT.XiFPaper.S1529OrbicurveGaloisCategoryActual
open LeanFormal.IUT.XiFPaper.S1319OrbicurveClauseActual

variable (l : PrimeGeFive)

/-- The actual represented finite-etale cover type of the S1419 orbicurve. -/
abbrev S1538Cover : Type 1 := S1529Cover l

/-- Exact first missing field: a Category instance on the cover type. -/
abbrev S1538CoverCategoryFirstMissing : Type 1 :=
  Category.{0, 1} (S1538Cover (l := l))

/-- The underlying CategoryStruct field of any such Category. -/
def S1538CategoryStructOfCategory
    (C : S1538CoverCategoryFirstMissing (l := l)) :
    CategoryStruct (S1538Cover (l := l)) :=
  C.toCategoryStruct

/-- Exact first missing surface (no inhabitant asserted). -/
def S1538CoverCategoryRequired : Type 1 :=
  S1538CoverCategoryFirstMissing (l := l)

/-- The remaining S1529 Galois-category inputs, retained exactly. -/
def S1538GaloisCategoryRemainingRequired : Prop :=
  ∀ C : S1538CoverCategoryFirstMissing (l := l),
    S1529GaloisCategoryRemaining (l := l) C

/-- Actual non-group prefix: the S1419 orbicurve is nonterminal with the
once-punctured signature. -/
theorem S1538Orbicurve_signature :
    (S1522Orbicurve (l := l)).signature =
      Iut.OrbicurveSignature.oncePuncturedElliptic :=
  S1522Orbicurve_signature l

theorem S1538Orbicurve_nonterminal :
    S1319NonterminalFiber (S1522Orbicurve (l := l)) :=
  S1522Orbicurve_nonterminal l

#check S1538Cover
#check S1538CoverCategoryFirstMissing
#check S1538CategoryStructOfCategory
#check S1538CoverCategoryRequired
#check S1538GaloisCategoryRemainingRequired
#check S1538Orbicurve_signature
#check S1538Orbicurve_nonterminal

end LeanFormal.IUT.XiFPaper.S1538OrbicurveCoverCategoryActual

end