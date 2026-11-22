import tmp.sheaf.xif.paper.S1419D6NonterminalStackActual
import tmp.sheaf.xif.paper.S1348D6OrbicurveActual
open LeanFormal.IUT CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
variable (l : PrimeGeFive)
#synth Category (Iut.SchemeOverField (S1348K l))
#synth Quiver (Iut.SchemeOverField (S1348K l))
#check (S1419AffineOver l ⟶ S1419AffineOver l)
