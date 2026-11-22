import tmp.sheaf.xif.paper.RepresentableCoverChosenCategoryActual
import tmp.sheaf.xif.paper.S1536SourceSignQuotientFromOrbicurveActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.RepresentableCoverChosenCategoryActual
open LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
noncomputable section
variable {l : PrimeGeFive}
example : (S1536XF (l := l)).stack.fiber = S1742YS (S1419AffineOver l) := rfl
