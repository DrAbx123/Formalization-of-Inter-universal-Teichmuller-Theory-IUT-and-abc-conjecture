import tmp.sheaf.xif.paper.S1267TensorUnitActual
import Mathlib.Algebra.Algebra.Pi
import Mathlib.RingTheory.SimpleRing.Basic

open scoped BigOperators

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1219ConcreteTensorLandingActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor

noncomputable section
universe upi umon ui
variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)

/-- Field-product decomposition proof that the diagonal insertion is a unit. -/
theorem concreteTensorLanding_isUnit_via_fieldProduct
    (q : CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place) (hq : q ≠ 0) :
    IsUnit (concreteTensorLanding I place q) := by
  classical
  obtain ⟨J, hJ, E, hfield, halgebra, e, hE, he, hinv⟩ :=
    exists_finiteNormedFieldProduct_piTensor (p := p)
      (A := fun _ : ConcreteIndex =>
        CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)
  letI := hJ
  letI : ∀ j, NontriviallyNormedField (E j) := hfield
  letI : ∀ j, NormedAlgebra ℚ_[p] (E j) := halgebra
  let e' : (PiTensorProduct ℚ_[p] (fun _ : ConcreteIndex =>
      CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)) ≃ₐ[ℚ_[p]]
      ((j : J) → E j) := e
  -- The diagonal insertion is the product of the single-factor insertions.
  have hD : concreteTensorLanding I place q =
      (∏ i : ConcreteIndex,
        PiTensorProduct.singleAlgHom (R := ℚ_[p])
          (A := fun _ : ConcreteIndex =>
            CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place) i q :
        ConcreteBlock I place) := by
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
    rfl
  have hD' : (show PiTensorProduct ℚ_[p] (fun _ : ConcreteIndex =>
      CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place) from
        concreteTensorLanding I place q) =
      ∏ i : ConcreteIndex,
        PiTensorProduct.singleAlgHom (R := ℚ_[p])
          (A := fun _ : ConcreteIndex =>
            CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place) i q :=
    hD
  -- Every component of e'(D q) is nonzero.
  have hcomp : ∀ j : J, e' (concreteTensorLanding I place q) j ≠ 0 := by
    intro j
    change e' (show PiTensorProduct ℚ_[p] (fun _ : ConcreteIndex =>
      CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place) from
        concreteTensorLanding I place q) j ≠ 0
    rw [hD']
    rw [map_prod]
    rw [Finset.prod_apply]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    let φ : CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place →ₐ[ℚ_[p]] E j :=
      (Pi.evalAlgHom ℚ_[p] E j).comp
        (e'.toAlgHom.comp (PiTensorProduct.singleAlgHom (R := ℚ_[p])
          (A := fun _ : ConcreteIndex =>
            CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place) i))
    have hφ : φ q = e' (PiTensorProduct.singleAlgHom (R := ℚ_[p])
        (A := fun _ : ConcreteIndex =>
          CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place) i q) j := rfl
    rw [← hφ]
    intro h
    apply hq
    apply RingHom.injective φ.toRingHom
    simpa using h
  -- Componentwise unit in the product of the fields.
  let u : (Π j : J, E j)ˣ :=
    MulEquiv.piUnits.symm
      (fun j => Units.mk0 (e' (concreteTensorLanding I place q) j) (hcomp j))
  have hu : (u : Π j : J, E j) = e' (concreteTensorLanding I place q) := by
    funext j
    rfl
  -- Transport the unit back through the algebra equivalence.
  let v : (ConcreteBlock I place)ˣ :=
    Units.map (e'.symm.toRingEquiv.toRingHom.toMonoidHom) u
  have hv : (v : ConcreteBlock I place) = concreteTensorLanding I place q := by
    change e'.symm (u : Π j : J, E j) = concreteTensorLanding I place q
    rw [hu, AlgEquiv.symm_apply_apply]
  rw [← hv]
  exact Units.isUnit v

end
