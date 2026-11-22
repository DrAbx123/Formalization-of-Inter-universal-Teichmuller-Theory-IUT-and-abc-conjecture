import tmp.sheaf.xif.paper.S1952HZeroActual

/-!
# S1986: the formal tensor-family transport closing `S1952TensorIntegrality`

## What S1952 left open

`S1952HZeroActual` reduces the actual C6 hull/unit equality to the tensor
integrality statement

    S1952TensorIntegrality l :
      arithmeticTensorTupleLogRegion (S1941ActualPlaces l) (S1941ActualTuple l)
        ⊆ arithmeticTupleCanonicalUnitReference (S1941ActualPlaces l) (S1941ActualTuple l),

and `S1952IntegralityFive` proves the *pointwise* integrality of the local log
shell at the concrete Gaussian five place,

    integralLogShell (K := concreteLogShellField) (p := 5) ⊆ Integers concreteLogShellField,

using the sharp odd-unramified bound `unitLog_mem_prime_smul_integers_of_odd_unramified`
and the proved irreducibility of the rational prime five in the actual integer
ring (`S1952FiveIrreducibleActual.s1952Five_irreducible`).  That proof runs at
the ofNat-5 scalar parameter, with the `NormedAlgebra ℚ_[5] concreteLogShellField`
structure transported from `ℚ_[concreteRationalPrime]` along
`concretePlace_rationalPrime_eq_five`.

## The formal gap that this file closes

The actual C6 tensor datum of the actual C3 is concrete:

* `S1941ActualPlaces l` is the tensor-place family `concretePlaces`, whose every
  value is `S1487FivePlace` (so every tensor factor is the single completion
  `CommonPrimeCompletion S1487FivePlace`);
* `S1941ActualTuple l` is the unique tuple `concreteTuple`;
* the tensor index is the finite type `FinitePrimePlace 2 7` and every factor
  index is `Unit`.

Hence, at the level of *types*, every tensor factor is definitionally the
concrete field:

    s1986FactorType_eq : CommonPrimeCompletion (S1941ActualPlaces l i (S1941ActualTuple l i))
                          = concreteLogShellField.

What is *not* definitional for the elaborator is the scalar parameter: the
tensor block is typed at the structure field `(S1941ActualC3 l).p`, which is
definitionally `5` (`s1986FactorPrime_eq`), but typeclass synthesis runs at
`instances` transparency, where the projections `S1941ActualC3` /
`actualSourcePilotRegionDataL` are not unfolded.  So the pointwise reduction
cannot simply be quoted at the literal tensor index; it is re-derived here at
that index.

## What is proved

1. `s1986FactorPlace_eq`, `s1986FactorType_eq`, `s1986FactorPrime_eq` — the
   tensor family is the constant concrete family, and its scalar parameter is
   the rational prime five.
2. `s1986IntegralLogShell_subset_integers` — the sharp odd-unramified bound
   re-run at an *arbitrary* odd prime index: for any `p ≠ 2` with `p`
   irreducible in `Integers K`, the log shell at `p` is integral.
3. `s1986FactorIrreducible` — irreducibility of the actual tensor-index prime
   in the actual factor integer ring, transported from
   `s1952Five_irreducible`: this is the pointwise-integrality input carried
   along the family congruence.
4. `s1986FactorIntegrality` — the pointwise integrality at every actual tensor
   factor, at the literal actual scalar index.
5. `s1986TensorIntegrality` — feeding (4) into the unconditional
   tensor-containment reduction `s1952TensorLogShellRegion_subset_unitReference_of_integral`
   gives `S1952TensorIntegrality l`.
6. `s1986HullVolume_eq_zero` and `s1986FirstMissing` — the hull unit
   log-volume `H` vanishes and `S1941FirstMissing l` holds, unconditionally.

No sorry, admit, axiom, arbitrary inhabitant, or replacement of the target by
`True` is used.  The `#print axioms` probes at the end record the axiom sets.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1986TensorTransportActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual
open LeanFormal.IUT.XiFPaper.S1941ActualQEquationActual
open LeanFormal.IUT.XiFPaper.S1952IntegralityFive
open LeanFormal.IUT.XiFPaper.S1952FiveIrreducibleActual
open LeanFormal.IUT.XiFPaper.S1952HZeroActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.LogShellLattice
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open MeasureTheory

local instance s1986GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance s1986FivePrime : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-! ## 1. The actual tensor family is the constant concrete family -/

/-- Every actual tensor place is the S1487 five place.  This is the concrete
value of the tensor-place family of the actual C3 (`concretePlaces` is the
constant family through the structure field). -/
theorem s1986FactorPlace_eq (l : PrimeGeFive) (i : (S1941ActualC3 l).tensorIndex) :
    (S1941ActualPlaces l) i ((S1941ActualTuple l) i) = S1487FivePlace := rfl

/-- The factor type of the actual C6 tensor block at every index is the concrete
Gaussian five completion: the family `fun i => CommonPrimeCompletion
(S1941ActualPlaces l i (S1941ActualTuple l i))` is the constant family
`fun _ => concreteLogShellField`. -/
theorem s1986FactorType_eq (l : PrimeGeFive) (i : (S1941ActualC3 l).tensorIndex) :
    CommonPrimeCompletion ((S1941ActualPlaces l) i ((S1941ActualTuple l) i)) =
      concreteLogShellField := rfl

/-- The scalar parameter of the actual tensor block is the rational prime five.
This is the `p`-index transport: the structure field is definitionally `5`,
although typeclass synthesis cannot see the projection unfold. -/
theorem s1986FactorPrime_eq (l : PrimeGeFive) : (S1941ActualC3 l).p = 5 := rfl

/-! ## 2. The pointwise integrality re-run at a literal prime index -/

/-- **The sharp odd-unramified shell bound at an arbitrary odd prime index.**
This is the argument of `S1952IntegralityFive.s1952IntegralLogShell_subset_integers`
with `5` replaced by the literal index `p`, so that it can be instantiated at
the actual tensor index `(S1941ActualC3 l).p` instead of the ofNat parameter
`5`. -/
theorem s1986IntegralLogShell_subset_integers
    {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
    [IsUltrametricDist K] [ProperSpace K] {p : ℕ} [Fact p.Prime]
    [NormedAlgebra ℚ_[p] K]
    (hp2 : p ≠ 2) (hpi : Irreducible (p : Integers K)) :
    (integralLogShell (K := K) (p := p) : Set K) ⊆ (Integers K : Set K) := by
  intro x hx
  rcases hx with ⟨u, rfl⟩
  change (logShellScale p : K)⁻¹ * unitLog (K := K) u ∈ Integers K
  have hmem := unitLog_mem_prime_smul_integers_of_odd_unramified (K := K) (p := p) hp2 hpi u
  rcases hmem with ⟨y, hy, hxy⟩
  have hxy' : (p : K) * y = unitLog (K := K) u := by
    simpa [smul_eq_mul] using hxy
  have hscale : (logShellScale p : K) = p := by simp [logShellScale, hp2]
  have hpne : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [hscale, ← hxy', inv_mul_cancel_left₀ hpne]
  exact hy

/-- The rational prime five is irreducible at the actual tensor index: the
proved irreducibility `s1952Five_irreducible` in the actual integer ring,
carried along the family congruence `s1986FactorType_eq` and the prime-index
transport `s1986FactorPrime_eq`. -/
theorem s1986FactorIrreducible (l : PrimeGeFive) (i : (S1941ActualC3 l).tensorIndex) :
    Irreducible ((S1941ActualC3 l).p : Integers (CommonPrimeCompletion
      ((S1941ActualPlaces l) i ((S1941ActualTuple l) i)))) :=
  s1952Five_irreducible

/-- The actual tensor index is odd. -/
theorem s1986FactorPrime_ne_two (l : PrimeGeFive) : (S1941ActualC3 l).p ≠ 2 := by
  have hp : (S1941ActualC3 l).p = 5 := rfl
  rw [hp]
  norm_num

/-- **Pointwise integrality at every actual C6 tensor factor**, at the literal
actual scalar index.  This is the pointwise statement of `S1952IntegralityFive`
transported to the factor type of the actual tensor block. -/
theorem s1986FactorIntegrality (l : PrimeGeFive) (i : (S1941ActualC3 l).tensorIndex) :
    (integralLogShell (K := CommonPrimeCompletion
      ((S1941ActualPlaces l) i ((S1941ActualTuple l) i)))
      (p := (S1941ActualC3 l).p) :
      Set (CommonPrimeCompletion ((S1941ActualPlaces l) i ((S1941ActualTuple l) i)))) ⊆
      (Integers (CommonPrimeCompletion
        ((S1941ActualPlaces l) i ((S1941ActualTuple l) i))) :
        Set (CommonPrimeCompletion ((S1941ActualPlaces l) i ((S1941ActualTuple l) i)))) :=
  s1986IntegralLogShell_subset_integers
    (K := CommonPrimeCompletion ((S1941ActualPlaces l) i ((S1941ActualTuple l) i)))
    (p := (S1941ActualC3 l).p) (s1986FactorPrime_ne_two l) (s1986FactorIrreducible l i)

/-! ## 3. The tensor-integrality statement and its two consequences -/

/-- **The exact tensor-integrality input of S1952 now holds unconditionally.**
The pointwise integrality of the tensor factors, applied through the
unconditional tensor-containment reduction, contains the actual tensor
log-shell region in the canonical unit reference. -/
theorem s1986TensorIntegrality (l : PrimeGeFive) : S1952TensorIntegrality l := by
  unfold S1952TensorIntegrality
  exact s1952TensorLogShellRegion_subset_unitReference_of_integral
    (places := S1941ActualPlaces l) (tuple := S1941ActualTuple l)
    (fun i => s1986FactorIntegrality l i)

/-- **The actual C6 hull unit log-volume vanishes**: `H = 0`. -/
theorem s1986HullVolume_eq_zero (l : PrimeGeFive) : S1941ActualHullVolume l = 0 :=
  s1952HullVolume_eq_zero_of_tensorIntegrality
    (places := S1941ActualPlaces l) (tuple := S1941ActualTuple l)
    (s1986TensorIntegrality l)

/-- **The exact arithmetic first missing of S1941 is closed.** -/
theorem s1986FirstMissing (l : PrimeGeFive) : S1941FirstMissing l :=
  s1952FirstMissing_of_tensorIntegrality l (s1986TensorIntegrality l)

/-- The first-missing statement is exactly the vanishing of the actual C6 hull
unit log-volume, restated for the consumers of S1941. -/
theorem s1986FirstMissing_iff_hullVolume_eq_zero (l : PrimeGeFive) :
    S1941FirstMissing l ↔ S1941ActualHullVolume l = 0 := Iff.rfl

/-! ## 4. Axiom probes -/

#print axioms s1986FactorPlace_eq
#print axioms s1986FactorType_eq
#print axioms s1986FactorPrime_eq
#print axioms s1986IntegralLogShell_subset_integers
#print axioms s1986FactorIrreducible
#print axioms s1986FactorIntegrality
#print axioms s1986TensorIntegrality
#print axioms s1986HullVolume_eq_zero
#print axioms s1986FirstMissing

end LeanFormal.IUT.XiFPaper.S1986TensorTransportActual
end
