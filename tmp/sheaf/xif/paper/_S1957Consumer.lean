/-
Consumer probe for S1957: loads the compiled olean of
`tmp.sheaf.xif.paper.S1957ActualCuspActual` and re-checks the exact target types.
-/
import tmp.sheaf.xif.paper.S1957ActualCuspActual

noncomputable section
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1913S1726CompactificationActual
open LeanFormal.IUT.XiFPaper.S1957ActualCuspActual

example : S1913AffineCompactification := S1957Compactification
example : Nonempty (OrbicurveBoundaryCusp S1726Orbicurve) := S1957ActualCusp
example : S1913RepresentableOpenImmersion S1957Compactification :=
  S1957RepresentableOpenImmersion

#check @S1957ActualCusp
#print axioms S1957ActualCusp

end
