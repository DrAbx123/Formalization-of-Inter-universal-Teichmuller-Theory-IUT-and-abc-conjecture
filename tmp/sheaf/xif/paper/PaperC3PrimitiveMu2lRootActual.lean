import tmp.sheaf.xif.paper.PaperC3ThetaValuesActual
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

-- Actual primitive 2l-th root of unity in ThetaExtension, from
-- HasEnoughRootsOfUnity.exists_primitiveRoot.  This is a mu_{2l} root of
-- unity, not a root of q.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.PaperC3PrimitiveMu2lRootActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaValuesActual

universe u v

variable {l : PrimeGeFive}
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {V : Type v} [Fintype V]
variable (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)
variable (v : V)

-- Actual primitive 2l-th root of unity.
noncomputable def primitiveMu2lRoot :
    PrimitiveMu2lRoot (G := G) v := by
  let h := HasEnoughRootsOfUnity.exists_primitiveRoot
    (ThetaExtension (G := G) v) (2 * l.value)
  let ζ := Classical.choose h
  have hζ : IsPrimitiveRoot ζ (2 * l.value) := Classical.choose_spec h
  exact {
    zeta := ζ
    zeta_pow := hζ.pow_eq_one
    primitive_order := by
      intro m hmpos hmlt hmone
      have hdvd : 2 * l.value ∣ m := (hζ.pow_eq_one_iff_dvd m).mp hmone
      have hle : 2 * l.value ≤ m := Nat.le_of_dvd hmpos hdvd
      exact absurd hle (not_le_of_gt hmlt) }

theorem primitiveMu2lRoot_zeta_pow :
    (primitiveMu2lRoot (G := G) v).zeta ^ (2 * l.value) = 1 :=
  (primitiveMu2lRoot (G := G) v).zeta_pow

theorem primitiveMu2lRoot_order
    (m : Nat) (hmpos : 0 < m) (hmlt : m < 2 * l.value) :
    (primitiveMu2lRoot (G := G) v).zeta ^ m ≠ 1 :=
  (primitiveMu2lRoot (G := G) v).primitive_order m hmpos hmlt

theorem primitiveMu2lRoot_mu2lAction_period
    (x : ThetaExtension (G := G) v) :
    mu2lAction (G := G) (primitiveMu2lRoot (G := G) v).toMu2lRoot (2 * l.value) x = x :=
  mu2lAction_period (G := G) (primitiveMu2lRoot (G := G) v).toMu2lRoot x

#check primitiveMu2lRoot
#check primitiveMu2lRoot_zeta_pow
#check primitiveMu2lRoot_order
#check primitiveMu2lRoot_mu2lAction_period

end LeanFormal.IUT.XiFPaper.PaperC3PrimitiveMu2lRootActual

end