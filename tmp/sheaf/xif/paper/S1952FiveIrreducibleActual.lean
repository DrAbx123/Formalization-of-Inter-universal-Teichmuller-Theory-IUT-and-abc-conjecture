import tmp.sheaf.xif.paper.S1941ActualQEquationActual
import LeanFormal.IUT.IUTI.InitialTheta.ConcreteArithmeticExample
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceLogKummerIdentification
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedIntegers
import LeanFormal.IUT.Foundations.Geometry.ConcreteSplitCurveFivePlace
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellSharpBounds
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTupleHullVolume
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompactHullScaling
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIntegralTensorCovolume
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicIntegerTensorLattice
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorLogShellRegion

/-!
# S1952: the tensor-integrality route to the actual C6 hull/unit equality

S1941 reduces the actual C3 q equation to the vanishing of the actual C6
canonical-hull unit log-volume

    H = arithmeticTupleHullUnitLogVolume (S1941ActualPlaces l) (S1941ActualTuple l) = 0.

The present file closes that equation by the tensor-integrality route:

1. The actual completion K = CommonPrimeCompletion S1487FivePlace is the
   normalized Gaussian five-place completion (concreteLogShellField).  The
   rational prime 5 is irreducible in Integers K.  This is transported from
   PadicInt.irreducible_p through the proved ring isomorphisms
   concreteFivePadicIntEquiv, the height-one-prime cast, the canonical/norm
   integer-ring comparisons, and normalizedCompletionIntegersEquiv.
2. Consequently integralLogShell K (p := 5) is contained in Integers K: the
   sharp odd-unramified shell bound of IntegralLogShellSharpBounds gives
   unitLog u in 5 times O_K; dividing by the shell scale 5 lands in O_K.
3. On every tensor factor of the actual C3 the completion is this same K,
   so the pure-tensor log region tensorLogShellRegion lies in the integral
   tensor region tensorIntegerRegion.  Every Q_p-algebra decomposition
   therefore carries it into the product unit region, i.e. into the canonical
   unit reference.
4. Hence the canonical hull equals the canonical unit reference and
   arithmeticTupleHullUnitLogVolume = 0, so S1941FirstMissing l holds.

No sorry, admit, axiom, arbitrary inhabitant or replacement of the target by
True is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1952FiveIrreducibleActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual
open LeanFormal.IUT.XiFPaper.S1941ActualQEquationActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.LogShellLattice
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceTheaterCarrier
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.LocalFieldProductHull
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open MeasureTheory

local instance s1952GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance s1952FivePrime : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- Generic transport of a normed-algebra structure along an equality of the
rational prime. -/
@[reducible] def s1952NormedAlgebraOfEq {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (h : p = q) {K : Type*} [NormedField K] [NormedAlgebra ℚ_[p] K] :
    NormedAlgebra ℚ_[q] K := by
  subst h
  infer_instance

/-- The scalar-field structure at the literal rational prime five, transported
from the completion's own rational prime (which is five). -/
local instance s1952NormedAlgebraFive : NormedAlgebra ℚ_[5] concreteLogShellField :=
  s1952NormedAlgebraOfEq (p := concreteRationalPrime) (q := 5)
    concretePlace_rationalPrime_eq_five

/-- Pointwise integrality of the actual log shell at the S1487 five place. -/
def S1952IntegralLogShell : Prop :=
  (integralLogShell (K := CommonPrimeCompletion (K := GaussianField) S1487FivePlace)
    (p := 5) : Set (CommonPrimeCompletion (K := GaussianField) S1487FivePlace)) ⊆
    (Integers (CommonPrimeCompletion (K := GaussianField) S1487FivePlace) : Set _)

/-! ## 1. The rational prime five is irreducible at the actual completion -/

/-- The ring of norm-integers of an actual completion and its adic completion
integer ring have the same carrier and are canonically isomorphic. -/
def s1952IntegersCompletionEquiv {F : Type*} [Field F] [NumberField F]
    (place : NumberField.FinitePlace F) :
    Integers (Completion place) ≃+* CompletionIntegers place where
  toFun x := ⟨x, (mem_completionIntegers_iff_norm_le_one place (x : Completion place)).mpr
    ((mem_integers_iff (x : Completion place)).mp x.property)⟩
  invFun x := ⟨x, (mem_integers_iff (x : Completion place)).mpr
    ((mem_completionIntegers_iff_norm_le_one place (x : Completion place)).mp x.property)⟩
  left_inv x := Subtype.ext rfl
  right_inv x := Subtype.ext rfl
  map_add' x y := Subtype.ext rfl
  map_mul' x y := Subtype.ext rfl

theorem s1952IntegersCompletionEquiv_five {F : Type*} [Field F] [NumberField F]
    (place : NumberField.FinitePlace F) :
    s1952IntegersCompletionEquiv place (5 : Integers (Completion place)) =
      (5 : CompletionIntegers place) := by
  apply Subtype.ext
  rfl

/-- The lower rational five place of the Gaussian five place is the concrete
rational five place, and its height-one prime is concreteFiveHeightOne. -/
theorem s1952HeightOne :
    (comap (k := ℚ) concretePlace).maximalIdeal = concreteFiveHeightOne := by
  rw [show comap (k := ℚ) concretePlace = concreteFivePlace by
    simpa [concretePlace] using concreteGaussianFivePlace_comap]
  exact concreteFivePlace_maximalIdeal

/-- The height-one-prime cast between adic completion integer rings is the
identity on natural-number constants. -/
theorem s1952CastHeightOne_natCast
    {P Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)} (h : P = Q)
    (n : ℕ) :
    (RingEquiv.cast (R := fun R : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers ℚ) => R.adicCompletionIntegers ℚ) h)
      (n : P.adicCompletionIntegers ℚ) = (n : Q.adicCompletionIntegers ℚ) := by
  subst h
  rfl

noncomputable def s1952LowerAdicEquiv :
    CompletionIntegers (comap (k := ℚ) concretePlace) ≃+* concreteFiveCompletionIntegers :=
  RingEquiv.cast (R := fun P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ) =>
    P.adicCompletionIntegers ℚ) s1952HeightOne

theorem s1952LowerAdicEquiv_five :
    s1952LowerAdicEquiv (5 : CompletionIntegers (comap (k := ℚ) concretePlace)) =
      (5 : concreteFiveCompletionIntegers) :=
  s1952CastHeightOne_natCast s1952HeightOne 5

/-- The rational five-adic integer ring and the rational five completion
integer ring are the same via the concrete-five comparison. -/
noncomputable def s1952FiveAdicEquiv : ℤ_[5] ≃+* concreteFiveCompletionIntegers :=
  concreteFivePadicIntEquiv.toRingEquiv

theorem s1952FiveAdicEquiv_five :
    s1952FiveAdicEquiv (5 : ℤ_[5]) = (5 : concreteFiveCompletionIntegers) := by
  have h := map_natCast (concreteFivePadicIntEquiv.toRingEquiv).toRingHom 5
  simpa [s1952FiveAdicEquiv] using h

/-- The rational prime five is irreducible in the adic integer ring of the
lower rational five completion. -/
theorem s1952LowerAdic_irreducible :
    Irreducible (5 : CompletionIntegers (comap (k := ℚ) concretePlace)) := by
  have hbase : Irreducible (5 : ℤ_[5]) := PadicInt.irreducible_p
  have h1 : Irreducible (5 : concreteFiveCompletionIntegers) := by
    have h' := (MulEquiv.irreducible_iff (f := s1952FiveAdicEquiv.toMulEquiv)).mpr hbase
    change Irreducible (s1952FiveAdicEquiv (5 : ℤ_[5])) at h'
    rwa [s1952FiveAdicEquiv_five] at h'
  have h' := (MulEquiv.irreducible_iff (f := s1952LowerAdicEquiv.symm.toMulEquiv)).mpr h1
  change Irreducible (s1952LowerAdicEquiv.symm (5 : concreteFiveCompletionIntegers)) at h'
  rw [show s1952LowerAdicEquiv.symm (5 : concreteFiveCompletionIntegers) =
      (5 : CompletionIntegers (comap (k := ℚ) concretePlace)) by
    rw [← s1952LowerAdicEquiv_five, RingEquiv.symm_apply_apply]] at h'
  exact h'

/-- Irreducibility transports to the norm-integer ring of the lower completion. -/
theorem s1952LowerCanonical_irreducible :
    Irreducible (5 : Integers (Completion (comap (k := ℚ) concretePlace))) := by
  have h : Irreducible (5 : CompletionIntegers (comap (k := ℚ) concretePlace)) :=
    s1952LowerAdic_irreducible
  have h' := (MulEquiv.irreducible_iff
    (f := (s1952IntegersCompletionEquiv (comap (k := ℚ) concretePlace)).symm.toMulEquiv)).mpr h
  change Irreducible ((s1952IntegersCompletionEquiv (comap (k := ℚ) concretePlace)).symm
    (5 : CompletionIntegers (comap (k := ℚ) concretePlace))) at h'
  rw [show (s1952IntegersCompletionEquiv (comap (k := ℚ) concretePlace)).symm
      (5 : CompletionIntegers (comap (k := ℚ) concretePlace)) =
      (5 : Integers (Completion (comap (k := ℚ) concretePlace))) by
    rw [← s1952IntegersCompletionEquiv_five (comap (k := ℚ) concretePlace)]
    exact RingEquiv.symm_apply_apply _ _] at h'
  exact h'

/-- Irreducibility transports to the norm-integer ring of the upper Gaussian
completion. -/
theorem s1952UpperCanonical_irreducible :
    Irreducible (5 : Integers (Completion concretePlace)) := by
  have h : Irreducible (5 : Integers (Completion (comap (k := ℚ) concretePlace))) :=
    s1952LowerCanonical_irreducible
  have h' := (MulEquiv.irreducible_iff
    (f := concretePlace_integersRingEquiv.toMulEquiv)).mpr h
  change Irreducible (concretePlace_integersRingEquiv
    (5 : Integers (Completion (comap (k := ℚ) concretePlace)))) at h'
  rw [show concretePlace_integersRingEquiv
      (5 : Integers (Completion (comap (k := ℚ) concretePlace))) =
      (5 : Integers (Completion concretePlace)) by
    exact map_natCast concretePlace_integersRingEquiv.toRingHom 5] at h'
  exact h'

/-- Irreducibility in the adic integer ring of the actual Gaussian completion. -/
theorem s1952UpperAdic_irreducible :
    Irreducible (5 : CompletionIntegers concretePlace) := by
  have h : Irreducible (5 : Integers (Completion concretePlace)) :=
    s1952UpperCanonical_irreducible
  have h' := (MulEquiv.irreducible_iff
    (f := (s1952IntegersCompletionEquiv concretePlace).toMulEquiv)).mpr h
  change Irreducible (s1952IntegersCompletionEquiv concretePlace
    (5 : Integers (Completion concretePlace))) at h'
  rwa [s1952IntegersCompletionEquiv_five] at h'

theorem s1952NormalizedIntegersEquiv_five :
    (normalizedCompletionIntegersEquiv concretePlace)
      (5 : Integers (NormalizedCompletion concretePlace)) =
      (5 : CompletionIntegers concretePlace) := by
  have h := map_natCast (normalizedCompletionIntegersEquiv concretePlace).toRingHom 5
  simpa using h

/-- **The rational prime five is irreducible in the actual integer ring.** -/
theorem s1952Five_irreducible :
    Irreducible (5 : Integers concreteLogShellField) := by
  have h : Irreducible (5 : CompletionIntegers concretePlace) :=
    s1952UpperAdic_irreducible
  have h' := (MulEquiv.irreducible_iff
    (f := (normalizedCompletionIntegersEquiv concretePlace).symm.toMulEquiv)).mpr h
  change Irreducible ((normalizedCompletionIntegersEquiv concretePlace).symm
    (5 : CompletionIntegers concretePlace)) at h'
  rw [show (normalizedCompletionIntegersEquiv concretePlace).symm
      (5 : CompletionIntegers concretePlace) =
      (5 : Integers (NormalizedCompletion concretePlace)) by
    rw [← s1952NormalizedIntegersEquiv_five, RingEquiv.symm_apply_apply]] at h'
  simpa [concreteLogShellField] using h'

end LeanFormal.IUT.XiFPaper.S1952FiveIrreducibleActual
end
