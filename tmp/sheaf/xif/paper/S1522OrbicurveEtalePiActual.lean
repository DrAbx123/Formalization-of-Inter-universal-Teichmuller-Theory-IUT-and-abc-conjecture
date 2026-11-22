import tmp.sheaf.xif.paper.S1511OrbicurvePiActual
import tmp.sheaf.xif.paper.S1490OrbicurveFundamentalGroupActual

-- S1522: first missing subfield of the S1419 OrbicurveEtaleFundamentalGroup.
-- The actual nonterminal orbicurve, actual once-punctured signature, and the
-- exact first missing structure: a category + GaloisCategory on the actual
-- OrbicurveFiniteEtaleCover.  No l-torsion/terminal/point fiber substitute.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1522OrbicurveEtalePiActual

open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1319OrbicurveClauseActual
open LeanFormal.IUT.XiFPaper.S1511OrbicurvePiActual
open LeanFormal.IUT.XiFPaper.S1490OrbicurveFundamentalGroupActual

variable (l : PrimeGeFive)

/-- The actual S1419 orbicurve. -/
noncomputable abbrev S1522Orbicurve : Iut.HyperbolicOrbicurve (S1348K l) :=
  S1419Orbicurve l

/-- Exact first missing subfield: an actual category structure on the actual
finite-etale cover type, together with the Galois-category certificate. -/
structure S1522GaloisCategoryFirstMissing where
  coverCategory : Category (Iut.OrbicurveFiniteEtaleCover (S1522Orbicurve (l := l)))
  galoisCategory :
    letI := coverCategory;
    @GaloisCategory (Iut.OrbicurveFiniteEtaleCover (S1522Orbicurve (l := l)))
      coverCategory

/-- Every full OrbicurveEtaleFundamentalGroup certificate has this first
missing subfield as its literal coverCategory/galoisCategory pair. -/
noncomputable def S1522GaloisCategoryFirstMissing_of_etalePi
    {G : ProfiniteGrp}
    (D : Iut.OrbicurveEtaleFundamentalGroup (S1522Orbicurve (l := l)) G) :
    S1522GaloisCategoryFirstMissing (l := l) where
  coverCategory := D.coverCategory
  galoisCategory := D.galoisCategory

/-- The full etale certificate type, retained exactly. -/
abbrev S1522EtalePiRequired (G : ProfiniteGrp) : Type 1 :=
  Iut.OrbicurveEtaleFundamentalGroup (S1522Orbicurve (l := l)) G

/-- Actual nonterminal certificate and actual once-punctured signature. -/
theorem S1522Orbicurve_signature :
    (S1522Orbicurve (l := l)).signature =
      Iut.OrbicurveSignature.oncePuncturedElliptic :=
  S1419Orbicurve_signature l

theorem S1522Orbicurve_nonterminal :
    S1319NonterminalFiber (S1522Orbicurve (l := l)) :=
  S1419NonterminalFiber l

/-- The exact S1511 group data over the absolute Galois group. -/
abbrev S1522GroupDataRequired : Type 1 :=
  S1511OrbicurvePiExactFirstField (l := l)

/-- The actual group-level product projection is available, but it is not a
finite-etale certificate and is not inserted into the group data. -/
theorem S1522ModelProjection_surjective :
    Function.Surjective (S1490ModelProjection (l := l)) :=
  S1490ModelProjection_surjective l

#check S1522Orbicurve
#check S1522GaloisCategoryFirstMissing
#check S1522GaloisCategoryFirstMissing_of_etalePi
#check S1522EtalePiRequired
#check S1522Orbicurve_signature
#check S1522Orbicurve_nonterminal
#check S1522GroupDataRequired
#check S1522ModelProjection_surjective

end LeanFormal.IUT.XiFPaper.S1522OrbicurveEtalePiActual

end