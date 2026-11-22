import tmp.sheaf.xif.paper.S1219ConcreteTensorLandingActual
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorFieldDecomposition
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Algebra.Pi
import Mathlib.RingTheory.SimpleRing.Basic

/-! # S1267: the actual tensor unit is the diagonal insertion

The concrete tensor block is the genuine commutative Q_p-algebra

  ConcreteBlock I place = tensor over Q_p of (i : FinitePrimePlace 2 7), L,

where L = CommonPrimeCompletion place.  Its multiplication is the
PiTensorProduct multiplication, which satisfies
tprod z * tprod w = tprod (z * w).

Consequently the diagonal insertion D q = tensor_i q of a nonzero q is an
actual unit, with explicit inverse D q^{-1} = tensor_i q^{-1}:

  D q * D q^{-1} = D (q * q^{-1}) = D 1 = 1.

This is the correct tensor unit for the q-landing law
tensorUnit = tensorLanding q: it is not the ring identity 1 and no ite or
arbitrary unit is used.  Classical.choice is used only to select the actual
q candidate whose existence is proved by finitePlaceQCandidate_nonempty; the
unit itself is the explicit diagonal insertion of that q.  The issue recorded
in S1219/S1239 is only that ConcreteBlock has no GroupWithZero instance, so
Units.mk0 is unavailable; Units.mkOfMulEqOne needs only Monoid and
IsDedekindFiniteMonoid, both supplied by CommRing, so it constructs the
explicit unit below.

We also cross-check the unit by the field-product decomposition
exists_finiteNormedFieldProduct_piTensor in the companion theorem
concreteTensorLanding_isUnit_via_fieldProduct.
-/

noncomputable section
set_option autoImplicit false
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1267TensorUnitActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1219ConcreteTensorLandingActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor

universe upi umon ui

variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)

/-- The concrete tensor block is a commutative ring; its multiplication is the
PiTensorProduct multiplication. -/
example : CommRing (ConcreteBlock I place) := inferInstance

/-- Multiplication of diagonal pure tensors. -/
theorem concreteTensorLanding_mul
    (z w : CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place) :
    concreteTensorLanding I place z * concreteTensorLanding I place w =
      concreteTensorLanding I place (z * w) := by
  change finitePadicTensorTprod (p := p)
      (M := fun _ : ConcreteIndex => CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)
      (fun _ => z) *
    finitePadicTensorTprod (p := p)
      (M := fun _ : ConcreteIndex => CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)
      (fun _ => w) =
    finitePadicTensorTprod (p := p)
      (M := fun _ : ConcreteIndex => CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)
      (fun _ => z * w)
  exact PiTensorProduct.tprod_mul_tprod (fun _ : ConcreteIndex => z)
    (fun _ : ConcreteIndex => w)

/-- The diagonal insertion of 1 is the ring identity. -/
theorem concreteTensorLanding_one :
    concreteTensorLanding I place
        (1 : CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place) = 1 := by
  change finitePadicTensorTprod (p := p)
      (M := fun _ : ConcreteIndex => CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)
      (fun _ => (1 : CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)) = 1
  exact (PiTensorProduct.one_def (R := ℚ_[p])
    (A := fun _ : ConcreteIndex => CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)).symm

/-- The actual unit attached to a nonzero diagonal insertion.  The inverse is
the diagonal insertion of the field inverse; no GroupWithZero is needed. -/
noncomputable def concreteTensorUnitOfNeZero
    (z : CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place) (hz : z ≠ 0) :
    (ConcreteBlock I place)ˣ :=
  Units.mkOfMulEqOne (concreteTensorLanding I place z)
    (concreteTensorLanding I place z⁻¹)
    (by
      rw [concreteTensorLanding_mul, mul_inv_cancel₀ hz, concreteTensorLanding_one])

/-- The underlying element of the unit is exactly the diagonal insertion. -/
@[simp] theorem concreteTensorUnitOfNeZero_val
    (z : CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place) (hz : z ≠ 0) :
    (concreteTensorUnitOfNeZero I place z hz : ConcreteBlock I place) =
      concreteTensorLanding I place z :=
  rfl

/-- The unit inverse is the diagonal insertion of the inverse. -/
@[simp] theorem concreteTensorUnitOfNeZero_inv_val
    (z : CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place) (hz : z ≠ 0) :
    ((concreteTensorUnitOfNeZero I place z hz).inv : ConcreteBlock I place) =
      concreteTensorLanding I place z⁻¹ :=
  rfl

/-- The unit is nonzero (it is an actual unit). -/
theorem concreteTensorUnitOfNeZero_ne_zero
    (z : CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place) (hz : z ≠ 0) :
    (concreteTensorUnitOfNeZero I place z hz : ConcreteBlock I place) ≠ 0 :=
  Units.ne_zero _

/-- The actual tensor unit attached to the actual q candidate: the diagonal
insertion of q.q.  The nonzero hypothesis is the source q-candidate field
q_ne_zero. -/
noncomputable def concreteTensorUnit (q : FinitePlaceQCandidate place.val) :
    (ConcreteBlock I place)ˣ :=
  concreteTensorUnitOfNeZero I place q.q q.q_ne_zero

/-- The q-landing law: the diagonal tensor landing of q.q is the actual
tensor unit.  This is definitional for the definition above. -/
theorem concreteTensorUnit_val_eq_landing (q : FinitePlaceQCandidate place.val) :
    (concreteTensorUnit I place q : ConcreteBlock I place) =
      concreteTensorLanding I place q.q :=
  rfl

/-- The actual q candidate at the supplied place. -/
noncomputable def concreteActualTensorUnit : (ConcreteBlock I place)ˣ :=
  concreteTensorUnit I place (Classical.choice (finitePlaceQCandidate_nonempty place.val))

/-- The actual tensor unit has an explicit inverse; it is not a fabricated
constant. -/
theorem concreteActualTensorUnit_mul_inv :
    (concreteActualTensorUnit I place : ConcreteBlock I place) *
      ((concreteActualTensorUnit I place).inv : ConcreteBlock I place) = 1 :=
  Units.mul_inv _

/-- The diagonal landing of the actual q is exactly the actual tensor unit. -/
theorem concreteActualTensorUnit_val_eq_landing :
    (concreteActualTensorUnit I place : ConcreteBlock I place) =
      concreteTensorLanding I place
        (Classical.choice (finitePlaceQCandidate_nonempty place.val)).q :=
  rfl

/-! ## Cross-check by the field-product decomposition

The following proves the same unit fact from
exists_finiteNormedFieldProduct_piTensor: the tensor block is an algebra
equivalent to a product of finite fields E j, each component of the diagonal
insertion is a product of values of injective field maps, and the
componentwise unit is assembled with the Mathlib pi-units equivalence. -/

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
  -- Componentwise unit in the product of the fields, assembled by piUnits.
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

/-- The unit produced by the field-product decomposition. -/
noncomputable def concreteTensorUnitViaFieldProduct
    (q : CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place) (hq : q ≠ 0) :
    (ConcreteBlock I place)ˣ :=
  (concreteTensorLanding_isUnit_via_fieldProduct I place q hq).unit

/-- Its underlying element is again the diagonal insertion. -/
theorem concreteTensorUnitViaFieldProduct_val
    (q : CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place) (hq : q ≠ 0) :
    (concreteTensorUnitViaFieldProduct I place q hq : ConcreteBlock I place) =
      concreteTensorLanding I place q :=
  IsUnit.unit_spec _

/-- The decomposition construction gives exactly the explicit unit; the unit
of a monoid with a fixed underlying value is unique. -/
theorem concreteTensorUnitViaFieldProduct_eq
    (q : CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place) (hq : q ≠ 0) :
    concreteTensorUnitViaFieldProduct I place q hq =
      concreteTensorUnitOfNeZero I place q hq :=
  Units.ext (by
    rw [concreteTensorUnitViaFieldProduct_val, concreteTensorUnitOfNeZero_val])


end LeanFormal.IUT.XiFPaper.S1267TensorUnitActual

end
