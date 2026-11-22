import tmp.sheaf.xif.paper.S2040QVPlaceSplitActual

/-!
# S2135: layer (1) qVPlace split status at the current (T, b)

The S2040 layer (1) split package asks for a rational place
v : FinitePrimePlace 2 7, a norm-preserving ring equivalence
Completion (qVPlace T b) ≃+* Completion (QPlace v), and the two arithmetic
conditions

  qVFamTensorRationalDegree T b = 1,
  localRamificationIndex (qVFamTensorPlace T b) = 1.

The source datum (T, b) supplies neither arithmetic condition, and b alone
does not determine the rational residue degree or ramification index of the
classically chosen lying-over lift nativeBadLift T.  The bad place b is only
a place of Fmod; nativeBadLift chooses one place of F above it, with no
degree-one or unramifiedness theorem.

This file records the exact status without assuming either condition:

* the unaligned package exposes only its own v and its two arithmetic
  fields (s2135_package_degree_one, s2135_package_unramified);
* the rational prime of the package's v lies in primeStrip 2 7, while b
  constrains only its residue characteristic (which is odd), not membership
  of qVFamTensorP T b in primeStrip 2 7
  (s2135_package_v_mem_primeStrip);
* the missing alignment datum is v.1 = qVFamTensorP T b
  (S2135PrimeAlignmentRequired);
* an aligned package forces qVFamTensorP T b into primeStrip 2 7, hence no
  aligned split package exists when the actual rational prime is outside
  that strip (s2135_aligned_prime_mem,
  s2135_no_aligned_package_of_prime_not_mem).

The construction direction (degree one + unramified + prime alignment gives
the package) and the converse degree/unramified consequences are recorded as
exact required data, not assumed.  No sorry, axiom, True/PUnit slot,
arbitrary inhabitant, or Nonempty gate is used. -/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 400000

namespace LeanFormal.IUT.XiFPaper.S2135Layer1SplitActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.TwoLthRootKummerActual
open LeanFormal.IUT.XiFPaper.S2040QVPlaceSplitActual
open LeanFormal.IUT.XiFPaper.S2040NormBridgeS2056Actual

universe u

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
  (b : Bad (nativePlaceSelection T))

/-! ## 1. The exact missing data -/

/-- The rational prime alignment not present in the source: the split
package's rational place v must have v.1 = qVFamTensorP T b. -/
def S2135PrimeAlignmentRequired : Prop :=
  qVFamTensorP T b ∈ primeStrip 2 7

/-- The local completion degree-one statement.  It is not supplied by the
source; it is the finrank form of the two arithmetic conditions. -/
def S2135CompletionFinrankOne : Prop :=
  Module.finrank
    ((comap (k := ℚ) (qVFamTensorPlace T b)).maximalIdeal.adicCompletion ℚ)
    ((qVFamTensorPlace T b).maximalIdeal.adicCompletion T.arithmetic.F) = 1

/-- The exact construction direction still missing at the current (T, b):
prime alignment together with the two arithmetic conditions would give the
local completion degree-one statement. -/
def S2135Layer1ConstructionRequired : Prop :=
  S2135PrimeAlignmentRequired (l := l) T b →
    S2040QVPlaceDegreeOneRequired T b →
      S2040QVPlaceUnramifiedRequired T b →
        S2135CompletionFinrankOne (l := l) T b

/-- The aligned layer (1) split datum: the existing S2040 split data plus
the explicit statement that its rational place is the one at the actual
rational prime qVFamTensorP T b. -/
structure S2135PrimeAlignedSplitData where
  data : S2040QVPlaceSplitData T b
  prime_eq : data.v.1 = qVFamTensorP T b

/-- The aligned full S2040 split package. -/
structure S2135PrimeAlignedSplitPackage where
  data : S2040QVPlaceSplitData T b
  prime_eq : data.v.1 = qVFamTensorP T b
  degree_one : S2040QVPlaceDegreeOneRequired T b
  unramified : S2040QVPlaceUnramifiedRequired T b

/-- The packaged aligned datum with the two arithmetic proofs. -/
noncomputable def s2135_packageOfAlignedData
    (P : S2135PrimeAlignedSplitData T b)
    (hdeg : S2040QVPlaceDegreeOneRequired T b)
    (hram : S2040QVPlaceUnramifiedRequired T b) :
    S2135PrimeAlignedSplitPackage T b :=
  { data := P.data, prime_eq := P.prime_eq, degree_one := hdeg, unramified := hram }

/-- The aligned package is an S2040 split package. -/
noncomputable def s2135_toPackage
    (P : S2135PrimeAlignedSplitPackage T b) :
    S2040QVPlaceSplitPackage T b :=
  { v := P.data.v
    completionEquiv := P.data.completionEquiv
    completion_isometry := P.data.completion_isometry
    degree_one := P.degree_one
    unramified := P.unramified }

/-! ## 2. What the unaligned package actually gives -/

/-- The package's rational place lies in the paper prime strip. -/
theorem s2135_package_v_mem_primeStrip
    (P : S2040QVPlaceSplitPackage T b) :
    P.v.1 ∈ primeStrip 2 7 :=
  P.v.2

/-- The package exposes the rational residue degree condition. -/
theorem s2135_package_degree_one
    (P : S2040QVPlaceSplitPackage T b) :
    S2040QVPlaceDegreeOneRequired T b :=
  P.degree_one

/-- The package exposes the local unramifiedness condition. -/
theorem s2135_package_unramified
    (P : S2040QVPlaceSplitPackage T b) :
    S2040QVPlaceUnramifiedRequired T b :=
  P.unramified

/-! ## 3. The aligned obstruction -/

/-- An aligned split package forces the actual rational prime under
qVPlace T b into the paper prime strip. -/
theorem s2135_aligned_package_prime_mem
    (P : S2135PrimeAlignedSplitPackage T b) :
    S2135PrimeAlignmentRequired (l := l) T b := by
  unfold S2135PrimeAlignmentRequired
  rw [← P.prime_eq]
  exact P.data.v.2

/-- If the actual rational prime is outside the paper prime strip, no
aligned split package exists. -/
theorem s2135_no_aligned_package_of_prime_not_mem
    (h : qVFamTensorP T b ∉ primeStrip 2 7) :
    IsEmpty (S2135PrimeAlignedSplitPackage T b) :=
  ⟨fun P => h (s2135_aligned_package_prime_mem T b P)⟩

/-- The aligned data exposes the same prime alignment. -/
theorem s2135_aligned_data_prime_eq
    (P : S2135PrimeAlignedSplitData T b) :
    P.data.v.1 = qVFamTensorP T b :=
  P.prime_eq

/-! ## 4. Axiom probes -/

#print axioms s2135_package_v_mem_primeStrip
#print axioms s2135_package_degree_one
#print axioms s2135_package_unramified
#print axioms s2135_aligned_package_prime_mem
#print axioms s2135_no_aligned_package_of_prime_not_mem
#print axioms s2135_aligned_data_prime_eq
#check S2135Layer1ConstructionRequired

end LeanFormal.IUT.XiFPaper.S2135Layer1SplitActual
end
