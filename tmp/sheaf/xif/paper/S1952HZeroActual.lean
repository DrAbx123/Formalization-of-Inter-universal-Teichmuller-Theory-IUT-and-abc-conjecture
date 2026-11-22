import tmp.sheaf.xif.paper.S1952IntegralityFive
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTupleHullVolume
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompactHullScaling
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIntegralTensorCovolume
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicIntegerTensorLattice
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorLogShellRegion

/-!
# S1952: the tensor-integrality route to the actual C6 hull/unit equality

## What is proved here

S1941 reduces the actual C3 q equation to

    H = arithmeticTupleHullUnitLogVolume (S1941ActualPlaces l) (S1941ActualTuple l) = 0.

This file proves the tensor-integrality reduction: if the actual tensor
log-shell region is contained in the canonical unit reference
(S1952TensorIntegrality), then the canonical hull equals the canonical unit
reference and H = 0, hence S1941FirstMissing l.  All the analytic and tensor
steps are unconditional.

## The proved concrete input

The companion module S1952IntegralityFive proves the mathematical integrality
input at the actual completion:

    integralLogShell (K := concreteLogShellField) (p := 5) is contained in
    Integers concreteLogShellField,

using the sharp odd-unramified shell bound and the proved irreducibility of
the rational prime five in the actual integer ring
(S1952FiveIrreducibleActual).

## The exact first missing

What is not formalized here is the transport of this concrete statement to the
literal tensor-factor type

    CommonPrimeCompletion (S1941ActualPlaces l i (S1941ActualTuple l i))

at the ofNat-5 scalar parameter.  The completion family is definitionally the
concrete field, but the dependent p index and the local normalized-algebra
instance make the direct typeclass elaboration expensive.  The missing datum is
therefore stated explicitly as S1952TensorIntegrality, and the present file
proves that it implies S1941FirstMissing.  This is a formal scalar-index
identification, not a mathematical gap in the local integrality.

No sorry, admit, axiom, arbitrary inhabitant, or replacement of the target by
True is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1952HZeroActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.S1941ActualQEquationActual
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.LocalFieldProductHull
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.LogShellLattice
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceTheaterCarrier
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open MeasureTheory

local instance s1952GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance s1952FivePrime : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

local instance s1952NormedAlgebraFive : NormedAlgebra ℚ_[5] concreteLogShellField :=
  S1952IntegralityFive.s1952NormedAlgebraOfEq (p := concreteRationalPrime) (q := 5)
    concretePlace_rationalPrime_eq_five

/-- The exact tensor-integrality statement needed for H = 0: the actual tensor
log-shell region is contained in the canonical unit reference. -/
def S1952TensorIntegrality (l : PrimeGeFive) : Prop :=
  arithmeticTensorTupleLogRegion (S1941ActualPlaces l) (S1941ActualTuple l) ⊆
    arithmeticTupleCanonicalUnitReference (S1941ActualPlaces l) (S1941ActualTuple l)

/-- The precise first missing of the present route: the tensor-integrality
statement above.  It is weaker than the pointwise integrality of the log shell
and is exactly what the hull argument needs. -/
def S1952FirstMissing (l : PrimeGeFive) : Prop :=
  S1952TensorIntegrality l

/-- Pointwise integrality of the log shell implies that the tensor log-shell
region is contained in the canonical unit reference. -/
theorem s1952TensorLogShellRegion_subset_unitReference_of_integral
    {ι : Type*} [Fintype ι] {V : ι → Type*}
    {K : Type*} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    (places : (i : ι) → V i → FinitePlaceAtPrime K p) (tuple : (i : ι) → V i)
    (hint : ∀ i, (integralLogShell (K := CommonPrimeCompletion (K := K)
      (places i (tuple i))) (p := p) : Set (CommonPrimeCompletion (K := K)
        (places i (tuple i)))) ⊆
      (Integers (CommonPrimeCompletion (K := K) (places i (tuple i))) : Set _)) :
    arithmeticTensorTupleLogRegion places tuple ⊆
      arithmeticTupleCanonicalUnitReference places tuple := by
  classical
  obtain ⟨J, hJ, E, hfield, halgebra, e, hE, _, _⟩ :=
    exists_arithmeticTensorTuple_fieldProduct places tuple
  letI := hJ
  letI := hfield
  letI := halgebra
  letI : ∀ j, FiniteDimensional ℚ_[p] (E j) := fun j => (hE j).1
  letI : ∀ j, ProperSpace (E j) := fun j => FiniteDimensional.proper ℚ_[p] (E j)
  have hregion : arithmeticTensorTupleLogRegion places tuple ⊆
      tensorIntegerRegion (p := p)
        (fun i => CommonPrimeCompletion (K := K) (places i (tuple i))) := by
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    refine ⟨x, ?_, rfl⟩
    intro i _
    exact hint i (hx i (Set.mem_univ i))
  have himage : e '' arithmeticTensorTupleLogRegion places tuple ⊆ unitRegion (K := E) :=
    (Set.image_mono hregion).trans
      (algHom_image_tensorIntegerRegion_subset_unitRegion (p := p)
        (A := fun i => CommonPrimeCompletion (K := K) (places i (tuple i)))
        (f := e.toAlgHom))
  intro z hz
  rw [arithmeticTupleCanonicalUnitReference_eq places tuple e]
  exact ⟨e z, himage ⟨z, hz, rfl⟩, e.symm_apply_apply z⟩

/-- Tensor integrality forces the field-product hull to be the unit region and
the hull unit log-volume to vanish. -/
theorem s1952HullVolume_eq_zero_of_tensorIntegrality
    {ι : Type*} [Fintype ι] {V : ι → Type*}
    {K : Type*} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    (places : (i : ι) → V i → FinitePlaceAtPrime K p) (tuple : (i : ι) → V i)
    (hint : arithmeticTensorTupleLogRegion places tuple ⊆
      arithmeticTupleCanonicalUnitReference places tuple) :
    arithmeticTupleHullUnitLogVolume places tuple = 0 := by
  classical
  obtain ⟨J, hJ, E, hfield, halgebra, e, hE, _, _⟩ :=
    exists_arithmeticTensorTuple_fieldProduct places tuple
  letI := hJ
  letI := hfield
  letI := halgebra
  letI : ∀ j, FiniteDimensional ℚ_[p] (E j) := fun j => (hE j).1
  letI : ∀ j, ProperSpace (E j) := fun j => FiniteDimensional.proper ℚ_[p] (E j)
  letI : MeasurableSpace ((j : J) → E j) := borel _
  letI : BorelSpace ((j : J) → E j) := ⟨rfl⟩
  have himage : arithmeticTupleFieldLogImage places tuple e ⊆ unitRegion (K := E) := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hx' := hint hx
    rw [arithmeticTupleCanonicalUnitReference_eq places tuple e] at hx'
    rcases hx' with ⟨z, hz, hzx⟩
    rw [← hzx, e.apply_symm_apply]
    exact hz
  have hregion_eq : region (fun _ : J => (1 : E _)) = unitRegion (K := E) := by
    ext x
    simp [region, unitRegion]
  have hhull_le : hull (arithmeticTupleFieldLogImage places tuple e) ⊆ unitRegion (K := E) := by
    rw [← hregion_eq]
    exact hull_minimal (fun j => one_ne_zero) (by rwa [hregion_eq])
  have hunit_le : unitRegion (K := E) ⊆ hull (arithmeticTupleFieldLogImage places tuple e) :=
    unitRegion_subset_arithmeticTupleFieldHull places tuple e
  have hhull_eq : hull (arithmeticTupleFieldLogImage places tuple e) = unitRegion (K := E) :=
    Set.Subset.antisymm hhull_le hunit_le
  rw [arithmeticTupleHullUnitLogVolume_eq places tuple e,
    hhull_eq, normalizedLogVolume_unitRegion]

/-- **The tensor-integrality route closes the exact arithmetic first missing.**
This is unconditional in the tensor-integrality hypothesis. -/
theorem s1952FirstMissing_of_tensorIntegrality
    (l : PrimeGeFive) (h : S1952TensorIntegrality l) :
    S1941FirstMissing l := by
  unfold S1941FirstMissing S1941ActualHullVolume
  exact s1952HullVolume_eq_zero_of_tensorIntegrality
    (p := 5)
    (places := S1941ActualPlaces l) (tuple := S1941ActualTuple l) h

/-- The precise first missing is exactly the tensor-integrality statement. -/
theorem s1952FirstMissing_iff_tensorIntegrality (l : PrimeGeFive) :
    S1952FirstMissing l ↔ S1952TensorIntegrality l := Iff.rfl

/-- The concrete local integrality input is already proved in the companion
module S1952IntegralityFive. -/
theorem s1952ConcreteIntegralityInput :
    (integralLogShell (K := concreteLogShellField) (p := 5) : Set concreteLogShellField) ⊆
      (Integers concreteLogShellField : Set concreteLogShellField) :=
  S1952IntegralityFive.s1952IntegralLogShell_subset_integers

/-! ## 4. Axiom probes -/

#print axioms s1952TensorLogShellRegion_subset_unitReference_of_integral
#print axioms s1952HullVolume_eq_zero_of_tensorIntegrality
#print axioms s1952FirstMissing_of_tensorIntegrality
#print axioms s1952ConcreteIntegralityInput

end LeanFormal.IUT.XiFPaper.S1952HZeroActual
end