import tmp.sheaf.xif.paper.S1267TensorUnitActual
import Mathlib.Algebra.Algebra.Pi

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1219ConcreteTensorLandingActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor

noncomputable section
open scoped BigOperators
universe upi umon ui
variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)

-- Try the diagonal product identity
example (q : CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place) :
    concreteTensorLanding I place q =
      ∏ i : ConcreteIndex,
        PiTensorProduct.singleAlgHom (R := ℚ_[p])
          (A := fun _ : ConcreteIndex =>
            CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place) i q := by
  classical
  change PiTensorProduct.tprod ℚ_[p] (fun _ => q) = _
  have hprod :
      (fun _ : ConcreteIndex => q) =
      (Finset.univ : Finset ConcreteIndex).prod (fun i =>
        MonoidHom.mulSingle
          (f := fun _ : ConcreteIndex =>
            CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place) i q) := by
    funext j
    rw [Finset.prod_apply]
    simp only [MonoidHom.mulSingle_apply, Pi.mulSingle_apply]
    rw [Finset.prod_ite_eq]
    simp
  rw [hprod]
  rw [PiTensorProduct.tprod_prod]
  simp only [PiTensorProduct.singleAlgHom_apply]

end