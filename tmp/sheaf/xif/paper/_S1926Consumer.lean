import tmp.sheaf.xif.paper.S1926RepresentableOpenImmersionActual

noncomputable section
open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S1913S1726CompactificationActual
open LeanFormal.IUT.XiFPaper.S1926RepresentableOpenImmersionActual

namespace S1926Consumer

/-- Target-locked consumer: for every compactification datum, the stack map of
the actual open immersion is representably an open immersion. -/
example : ∀ C : S1913AffineCompactification,
    Nonempty (EtaleStackOpenImmersion C.S1913StackOpenMap) :=
  fun C => ⟨S1926OpenImmersion C⟩

/-- Target-locked consumer: S1913RepresentableOpenImmersion is closed. -/
example : ∀ C : S1913AffineCompactification,
    S1913RepresentableOpenImmersion C :=
  S1926RepresentableOpenImmersion

/-- Consumer: the actual cusp from a compactification datum. -/
example (C : S1913AffineCompactification) :
    Nonempty (OrbicurveBoundaryCusp LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual.S1726Orbicurve) :=
  S1926Cusp_of_compactification C

#print axioms S1926RepresentableOpenImmersion
#print axioms S1926OpenImmersion

end S1926Consumer
