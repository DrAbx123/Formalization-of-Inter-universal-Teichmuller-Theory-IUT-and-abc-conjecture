import tmp.sheaf.xif.paper.S1777AffineCoverAlgebrasActual
import Mathlib.RingTheory.Etale.Finite

noncomputable section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1777AffineCoverAlgebrasActual

namespace M1

noncomputable def sliceAlgebra (X : S1733Slice) : S1777Algᵒᵖ :=
  letI : Algebra S1777R (↥X.left.unop) := (S1777AlgMap X).hom.toAlgebra
  letI : Module.Finite S1777R (↥X.left.unop) := by
    rw [← RingHom.finite_algebraMap, RingHom.algebraMap_toAlgebra]
    exact S1777AlgMap_finite X
  letI : Algebra.Etale S1777R (↥X.left.unop) := by
    rw [← RingHom.etale_algebraMap, RingHom.algebraMap_toAlgebra]
    exact S1777AlgMap_etale X
  Opposite.op (CommAlgCat.FiniteEtale.of S1777R (↥X.left.unop))

-- test: the objects are equal
example (X : S1733Slice) : (sliceAlgebra X).unop.obj = CommAlgCat.of S1777R (↥X.left.unop) := rfl

end M1
