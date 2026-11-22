/- U-L actual Phi realization: every actual source-arrow linear realization of the
packet (unit-layer/log exchange, lattice preservation) lies in the actual
lattice-preserving action family p6Phi. -/
import tmp.sheaf.xif.paper.Mzk1P6PhiActionFamilyActual
import tmp.sheaf.xif.paper.Mzk1ULActualRootActual
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicIntegralLattice
import Mathlib.Tactic
noncomputable section
open scoped BigOperators
open scoped LeanFormal.IUT.FinitePadicIntegralLattice
namespace LeanFormal.IUT.XiFPaper.Mzk1ULPhiRealizationActual
open LeanFormal.IUT LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.Mzk1P6PhiActionFamilyActual
universe u v w
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {V : ι → Type w} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
variable (tuple : (i : ι) → V i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
/-- The packet's fixed log-square invariant: the sum of squared shell
ramification exponents over the actual tensor places. -/
noncomputable def ulLogSquare : Real :=
  ∑ i : ι, (logShellRamificationExponent
      (K := CommonPrimeCompletion (places i (tuple i))) (p := p) : Real) ^ 2
/-- An actual linear realization of a source arrow: a `ℚ_p`-linear equivalence
of the tensor block whose unit-layer/log exchange diagram makes it preserve the
unit log lattice. -/
structure ULSourceArrowRealization where
  phi : ArithmeticTensorTupleBlock places tuple ≃ₗ[ℚ_[p]]
    ArithmeticTensorTupleBlock places tuple
  /-- Unit-layer/log exchange: the actual unit log lattice is mapped into itself. -/
  unit_layer_exchange : ∀ u, u ∈ arithmeticTupleUnitLogLattice places tuple →
    phi u ∈ arithmeticTupleUnitLogLattice places tuple
/-- The linear realization of a source arrow belongs to the actual Phi action
family p6Phi. -/
theorem ulSourceArrowRealization_mem_p6Phi
    (R : ULSourceArrowRealization places tuple) : R.phi ∈ p6Phi places tuple :=
  R.unit_layer_exchange
/-- Actual Phi realization attached to a source arrow: its linear part, the
membership proof in p6Phi, the fixed log-square invariant, and lattice
preservation. -/
structure ULPhiRealization where
  phi : ArithmeticTensorTupleBlock places tuple ≃ₗ[ℚ_[p]]
    ArithmeticTensorTupleBlock places tuple
  mem_p6Phi : phi ∈ p6Phi places tuple
  log_square : Real
  log_square_eq : log_square = ulLogSquare (p := p) places tuple
  lattice_preserved : ∀ u, u ∈ arithmeticTupleUnitLogLattice places tuple →
    phi u ∈ arithmeticTupleUnitLogLattice places tuple
/-- Realize each actual source arrow as an element of the actual action family. -/
noncomputable def ulPhiRealizationOfSourceArrow
    (R : ULSourceArrowRealization places tuple) : ULPhiRealization places tuple where
  phi := R.phi
  mem_p6Phi := ulSourceArrowRealization_mem_p6Phi places tuple R
  log_square := ulLogSquare (p := p) places tuple
  log_square_eq := rfl
  lattice_preserved := R.unit_layer_exchange
/-- Source coverage: every element of the actual action family is the linear
realization of a source arrow (take its own unit-layer exchange diagram). -/
theorem ulPhiRealization_cover
    (phi : ArithmeticTensorTupleBlock places tuple ≃ₗ[ℚ_[p]]
      ArithmeticTensorTupleBlock places tuple)
    (hphi : phi ∈ p6Phi places tuple) :
    ∃ R : ULSourceArrowRealization places tuple, R.phi = phi :=
  ⟨{ phi := phi, unit_layer_exchange := hphi }, rfl⟩
/-- The identity action is realized by an actual source arrow. -/
noncomputable def ulSourceArrowRealizationIdentity :
    ULSourceArrowRealization places tuple where
  phi := LinearEquiv.refl ℚ_[p] (ArithmeticTensorTupleBlock places tuple)
  unit_layer_exchange := by
    intro u hu
    simpa using hu
/-- The identity realization is the identity action, with the fixed log square. -/
noncomputable def ulPhiRealizationIdentity : ULPhiRealization places tuple :=
  ulPhiRealizationOfSourceArrow places tuple
    (ulSourceArrowRealizationIdentity places tuple)
section CoordinateAction
variable (c : ℤ_[p])
/-- Concrete source-arrow coordinate action: multiplication by the nonzero p-adic
integer `c`, i.e. the diagonal matrix `c · 1` in any `ℚ_p`-basis of the tensor
block. -/
noncomputable def ulScalarActionEquiv (hc : (c : ℚ_[p]) ≠ 0) :
    ArithmeticTensorTupleBlock places tuple ≃ₗ[ℚ_[p]]
      ArithmeticTensorTupleBlock places tuple :=
  LinearEquiv.smulOfNeZero ℚ_[p] (ArithmeticTensorTupleBlock places tuple) (c : ℚ_[p]) hc
/-- The scalar coordinate action is exactly `x ↦ c • x`. -/
theorem ulScalarActionEquiv_apply (hc : (c : ℚ_[p]) ≠ 0)
    (x : ArithmeticTensorTupleBlock places tuple) :
    ulScalarActionEquiv places tuple c hc x = (c : ℚ_[p]) • x := rfl
/-- Every `ℤ_p`-integer scalar coordinate action preserves the unit log lattice:
the lattice is a `ℤ_p`-submodule and the `ℚ_p`-scalar `c` is the p-adic integer
`c` under the scalar tower. -/
theorem ulScalarActionEquiv_mem_unitLogLattice (hc : (c : ℚ_[p]) ≠ 0)
    (x : ArithmeticTensorTupleBlock places tuple)
    (hx : x ∈ arithmeticTupleUnitLogLattice places tuple) :
    ulScalarActionEquiv places tuple c hc x ∈
      arithmeticTupleUnitLogLattice places tuple := by
  rw [ulScalarActionEquiv_apply places tuple c hc x]
  have htower : (c : ℚ_[p]) • x = c • x := by
    rw [← LeanFormal.IUT.FinitePadicIntegralLattice.padicInteger_smul_eq c x]
  rw [htower]
  exact Submodule.smul_mem _ c hx
/-- The concrete p-adic integer scalar source arrow: its linear part is the
diagonal coordinate action, and its unit-layer exchange is proved from the
`ℤ_p`-module structure of the lattice (not by unfolding `p6Phi`). -/
noncomputable def ulSourceArrowRealizationScalar (hc : (c : ℚ_[p]) ≠ 0) :
    ULSourceArrowRealization places tuple where
  phi := ulScalarActionEquiv places tuple c hc
  unit_layer_exchange := fun x hx =>
    ulScalarActionEquiv_mem_unitLogLattice places tuple c hc x hx
/-- The concrete scalar source arrow, realized in the actual action family with
the fixed log-square invariant. -/
noncomputable def ulPhiRealizationScalar (hc : (c : ℚ_[p]) ≠ 0) :
    ULPhiRealization places tuple :=
  ulPhiRealizationOfSourceArrow places tuple
    (ulSourceArrowRealizationScalar places tuple c hc)
end CoordinateAction
#print axioms ulScalarActionEquiv_apply
#print axioms ulScalarActionEquiv_mem_unitLogLattice
#print axioms ulSourceArrowRealizationScalar
#print axioms ulPhiRealizationScalar
#print axioms ulLogSquare
#print axioms ulSourceArrowRealization_mem_p6Phi
#print axioms ulPhiRealizationOfSourceArrow
#print axioms ulPhiRealization_cover
#print axioms ulPhiRealizationIdentity
end LeanFormal.IUT.XiFPaper.Mzk1ULPhiRealizationActual
end
