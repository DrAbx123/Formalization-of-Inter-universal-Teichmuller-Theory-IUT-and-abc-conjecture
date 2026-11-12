# S1986: the formal tensor-family transport closing S1952TensorIntegrality

Date: 2026-11-01. Task: complete the formal transport that S1952HZeroActual
isolated as its exact first missing —

    S1952TensorIntegrality l :
      arithmeticTensorTupleLogRegion (S1941ActualPlaces l) (S1941ActualTuple l)
        ⊆ arithmeticTupleCanonicalUnitReference (S1941ActualPlaces l) (S1941ActualTuple l)

— by carrying the pointwise integrality of S1952IntegralityFive through the
tensor-family / p-index transport, and hence prove S1941FirstMissing and H = 0.
Do not fake.

Result: **proved**, unconditionally in l.

    s1986TensorIntegrality     : ∀ l : PrimeGeFive, S1952TensorIntegrality l
    s1986HullVolume_eq_zero    : ∀ l : PrimeGeFive, S1941ActualHullVolume l = 0
    s1986FirstMissing          : ∀ l : PrimeGeFive, S1941FirstMissing l

No new hypothesis, no axiom, no sorry/admit, no replacement of the target.

## 1. What the tensor data actually are

For the actual C3 (= S1487FaithfulC3 l = S1391 actualSourcePilotRegionDataL at
S1487FivePlace) the C6 tensor block is the concrete diagonal one:

* tensorIndex = ConcreteIndex = FinitePrimePlace 2 7;
* tensorPlaceIndex i = Unit; tensorTuple i = ();
* tensorPlaces i a = concretePlaces i a = S1487FivePlace.

Hence, at the level of types, every tensor factor is the concrete field, and
this is definitional (proved by rfl):

    s1986FactorPlace_eq : (S1941ActualPlaces l) i ((S1941ActualTuple l) i) = S1487FivePlace
    s1986FactorType_eq  : CommonPrimeCompletion (S1941ActualPlaces l i (S1941ActualTuple l i))
                            = concreteLogShellField
    s1986FactorPrime_eq : (S1941ActualC3 l).p = 5

So the family congruence that S1952 asked for is rfl at the type level, and the
scalar parameter is rfl-equal to five.

## 2. The actual obstruction (research fact)

The obstruction is *not* mathematical and *not* a type-level difference. It is
a **typeclass-transparency** artifact:

* the tensor block ArithmeticTensorTupleBlock (S1941ActualPlaces l)
  (S1941ActualTuple l) is typed at the structure field (S1941ActualC3 l).p, so
  arithmeticTensorTupleLogRegion synthesizes the factor instance as
  commonPrimeCompletionNormedAlgebra (places i (tuple i)), i.e. at the literal
  index (S1941ActualC3 l).p;
* typeclass synthesis runs at `instances` transparency, where the projections
  S1941ActualC3 / S1487FaithfulC3 / actualSourcePilotRegionDataL are not
  unfolded. Therefore the transported instance
  s1952NormedAlgebraOfEq (p := concreteRationalPrime) (q := 5) ..., which is the
  one used by S1952IntegralityFive, is **not** findable at the tensor index, and
  the concrete theorem cannot simply be quoted there. Forcing the exercise
  (inferInstanceAs (NormedAlgebra ℚ_[5] concreteLogShellField) at the factor
  type) ends in a kernel deterministic timeout.

That is exactly the 'formal p-index transport' that S1952HZeroActual recorded as
its first missing; it is a genuine formal artifact, not a gap in the local
integrality.

## 3. The fix

Re-run the sharp odd-unramified argument at a *literal* odd prime index instead
of transporting the instance:

1. s1986IntegralLogShell_subset_integers — the argument of
   s1952IntegralLogShell_subset_integers with 5 replaced by a variable p: for
   any p ≠ 2 with Irreducible (p : Integers K),
   integralLogShell (K := K) (p := p) ⊆ Integers K. It is instantiated at the
   actual factor type using the *actual* (global) normed-algebra instance, so no
   instance transport is needed.
2. s1986FactorIrreducible — irreducibility of the actual index prime in the
   actual factor integer ring, transported from the proved concrete
   s1952Five_irreducible (Integers depends only on the NormedField and
   ultrametric structures, so this single default-transparency defeq check is
   cheap and goes through by plain exact).
3. s1986FactorPrime_ne_two — the actual index is odd (rfl to 5, then norm_num).
4. s1986FactorIntegrality — the pointwise integrality at every actual tensor
   factor, at the literal actual index.

Then the two unconditional S1952 reductions are applied unchanged:

* s1952TensorLogShellRegion_subset_unitReference_of_integral (per-factor
  integrality implies tensor log-shell region ⊆ canonical unit reference) gives
  s1986TensorIntegrality;
* s1952HullVolume_eq_zero_of_tensorIntegrality gives H = 0
  (s1986HullVolume_eq_zero);
* s1952FirstMissing_of_tensorIntegrality gives S1941FirstMissing l
  (s1986FirstMissing).

## 4. Lean artifact

Target file:
  tmp/sheaf/xif/paper/S1986TensorTransportActual.lean
  bytes 10754,
  SHA256 24D5E1DD36D0E4305FCEBD42430BBC7E2A6C3EAED0B237A320928536721CF2EE.

Compile (from D:\lean):

    lake env lean tmp/sheaf/xif/paper/S1986TensorTransportActual.lean

  EXIT=0. Log: tmp/sheaf/xif/paper/_S1986_final.log.

Olean:

    lake env lean -j1 -R D:/lean
      -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1986TensorTransportActual.olean
      tmp/sheaf/xif/paper/S1986TensorTransportActual.lean

  EXIT=0. Log: tmp/sheaf/xif/paper/_S1986_olean.log.
  .lake/build/lib/lean/tmp/sheaf/xif/paper/S1986TensorTransportActual.olean
  bytes 115904,
  SHA256 35F8A1000921808E17A361E9A5E0007F541132EED2ED477F0C9EE4E0A2176F8F.

All 9 public declarations probed with #print axioms depend only on
[propext, Classical.choice, Quot.sound]:

    s1986FactorPlace_eq, s1986FactorType_eq, s1986FactorPrime_eq,
    s1986IntegralLogShell_subset_integers, s1986FactorIrreducible,
    s1986FactorIntegrality, s1986TensorIntegrality, s1986HullVolume_eq_zero,
    s1986FirstMissing.

Consumer probe: tmp/sheaf/xif/paper/_S1986ConsumerCheck.lean EXIT=0. It imports
the olean and derives the actual C3 q equation

    consumer_actualQEquation (l) : S1941ActualQEquation l

from s1941ActualQEquation_iff_firstMissing and s1986FirstMissing; its axiom set
is again [propext, Classical.choice, Quot.sound].

## 5. Boundary

* target_accepted = false for the whole project: this closes the S1941/S1952
  arithmetic first missing with the S1952 reductions unchanged, but the usual
  project-level acceptance (versioned full build, comparator acceptance,
  transitive axiom audit, source-semantics review) is not run here.
* No fake normalization, arbitrary data, axiom, sorry, True or PUnit.
* Not run: full project build, comparator acceptance, independent review.
* Suggested ledger entry: the failed route is 'quote
  s1952IntegralLogShell_subset_integers directly at the tensor index (or force
  the transported NormedAlgebra instance there)'; the effective shortcut is
  'restate the pointwise input generically in the prime index and transport only
  the irreducibility, which lives at the Integers level'.
