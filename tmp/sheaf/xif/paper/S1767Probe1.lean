import tmp.sheaf.xif.paper.S1767FiniteEtaleGaloisNoSorryActual

open CategoryTheory CategoryTheory.Limits
open S1767FiniteEtaleGalois

namespace S1767ImportProbe

variable {K : Type} [Field K]
  (hQuot : HasQuotientsByFiniteGroupsField K)
  (hMono : MonoInducesIsoOnDirectSummandField K)
  (hFiber : FiberFunctorField K (preGaloisCategory (K := K) hQuot hMono))

example : PreGaloisCategory ((CommAlgCat.FiniteEtale.{0} K)ᵒᵖ) := preGaloisCategory hQuot hMono

example : GaloisCategory ((CommAlgCat.FiniteEtale.{0} K)ᵒᵖ) := galoisCategory hQuot hMono hFiber

example : HasPullbacks ((CommAlgCat.FiniteEtale.{0} K)ᵒᵖ) := inferInstance

example : HasFiniteCoproducts ((CommAlgCat.FiniteEtale.{0} K)ᵒᵖ) := inferInstance

example : HasTerminal ((CommAlgCat.FiniteEtale.{0} K)ᵒᵖ) := inferInstance

end S1767ImportProbe
