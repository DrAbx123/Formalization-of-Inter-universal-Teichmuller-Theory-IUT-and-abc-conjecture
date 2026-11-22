/- PROBE: StepV possible images for the singleton `{LinearEquiv.refl}` (the concrete
construction `istar := (), varpi := generator, Phi := {refl}`): the possible images are exactly
the `varpi`-translate of `O_hol`.
NOTE (search): `urCeilGenerator`/`urCeilC`/`thetaTensorScaledRegion`/`urLabelOneRegion`/
`urNonzeroLabelHull` do NOT exist anywhere in D:\lean (0 hits), so the requested `thetaTensorScaledRegion`
form cannot be stated yet; this file proves the reusable core that identifies the image set with
the translate, after which the region identification is `arithCanonicalUnitReference = O_hol` +
fractional-lattice equality (both existing donors). Direct `lake env lean`. -/
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceStepVAssembly
import Mathlib.Tactic

set_option maxHeartbeats 2000000

noncomputable section
open LeanFormal.IUT.NumberFieldFinitePlace

universe u v w
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] [DecidableEq ι] {V : ι → Type w}
variable {places : (i : ι) → V i → FinitePlaceAtPrime K p} {tuple : (i : ι) → V i}

/-- **Possible images for `Phi = {refl}`**: they are exactly the `ϖ`-translate of `O_hol`. -/
theorem stepVPossibleImages_singleton_refl
    (istar : ι) (varpi : CommonPrimeCompletion (places istar (tuple istar))) :
    arithmeticTupleStepVPossibleImages (p := p) places tuple istar varpi
        ({(AlgEquiv.refl ℚ_[p] (ArithmeticTensorTupleBlock places tuple)).toLinearEquiv} :
          Set (ArithmeticTensorTupleBlock places tuple ≃ₗ[ℚ_[p]]
            ArithmeticTensorTupleBlock places tuple)) =
      (fun x => arithmeticTupleTprod places tuple (Function.update 1 istar varpi) * x) ''
        arithmeticTupleCanonicalUnitReference places tuple := by
  ext s
  constructor
  · rintro ⟨φ, hφ, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at hφ
    subst hφ
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(AlgEquiv.refl ℚ_[p] (ArithmeticTensorTupleBlock places tuple)).toLinearEquiv,
      rfl, x, hx, ?_⟩
    simp

#print axioms stepVPossibleImages_singleton_refl
end