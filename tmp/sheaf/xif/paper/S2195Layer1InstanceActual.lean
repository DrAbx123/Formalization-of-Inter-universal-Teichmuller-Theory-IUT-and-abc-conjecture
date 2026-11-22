import tmp.sheaf.xif.paper.S2135Layer1SplitActual
import LeanFormal.IUT.ABCBridge.Geometry.RelativeCompletionFinrankReduction
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceFullPrimePacket

/-!
# S2195: layer (1) instance alignment and dependent cast, actual

S2135 recorded the layer (1) split obstruction at the actual (T, b):

* the S2040 degree-one condition is stated with
  ArithmeticQPilotBaseChange.localResidueDegree, while the completion degree
  identity uses NumberFieldFinitePlace.relativeResidueDegree; these are
  distinct constants with the same value;
* the unramified condition is stated with the *local* ramification index of
  the completed valuation rings (NumberFieldFinitePlace.localRamificationIndex),
  while the completion identity is stated with the library relative index
  relativeRamificationIndex; the two are aligned by
  localRamificationIndex_eq_relativeRamificationIndex (and the residue degree
  by localInertiaDegree_eq_relativeResidueDegree);
* transporting the resulting completion degree/equivalence to
  S2046CompletionOUnitsActual.QPlace v requires a dependent cast along
  comap (k := Q) (qVFamTensorPlace T b) = QPlace v, whose rational prime is
  v.1; the Fact (Nat.Prime v.1) instance is not registered globally in the
  S2046 file (its instance is file-local), and b supplies no
  qVFamTensorP T b in primeStrip 2 7.

This file implements exactly those alignments and the cast, and then proves:

* s2195_layer1ConstructionRequired : S2135Layer1ConstructionRequired T b
  unconditionally: the completion degree at the actual qVPlace is one as soon
  as the two arithmetic conditions f = 1 and e = 1 hold.  The proof uses
  finrank_adicCompletion_eq_relativeCompletionDegree_unconditional; no
  hypothesis is added, no sorry/axiom/True-slot is used.

* s2195_completionEquivOfPlace: the completion degree-one identity yields a
  ring equivalence Completion (qVPlace T b) to Completion q for *any*
  rational place q equal to the contraction (in particular for
  q = QPlace v), and it is isometric for the canonical completion norms.

* s2195_primeAlignedSplitPackage: given v : FinitePrimePlace 2 7 with
  v.1 = qVFamTensorP T b together with the two arithmetic conditions, the
  full aligned S2135 split package is constructed.  Consequently a split
  package exists exactly when qVFamTensorP T b is in primeStrip 2 7 (existence
  is s2195_exists_primeAlignedSplitPackage; the converse obstruction is S2135's
  s2135_no_aligned_package_of_prime_not_mem).  The source b does not provide
  that membership, so this is the exact remaining first missing input.

No axiom, sorry, True/PUnit slot, arbitrary inhabitant, or Nonempty gate is
used. -/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2195Layer1InstanceActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamTensorBlockAlignmentActual
open LeanFormal.IUT.XiFPaper.TwoLthRootKummerActual
open LeanFormal.IUT.XiFPaper.S2040QVPlaceSplitActual
open LeanFormal.IUT.XiFPaper.S2040NormBridgeS2056Actual
open LeanFormal.IUT.XiFPaper.S2046CompletionOUnitsActual
open LeanFormal.IUT.XiFPaper.S2135Layer1SplitActual

universe u

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
  (b : Bad (nativePlaceSelection T))

/-! ## 1. Instance alignment -/

/-- The Fact (Nat.Prime v.1) instance for a prime-strip place.  The S2046 file
only declares the corresponding instance as a file-local instance, so the
transport to QPlace v needs it registered here. -/
instance s2195FactPrime (v : FinitePrimePlace 2 7) : Fact (Nat.Prime v.1) :=
  ⟨v.2.2.2⟩

/-- The rational residue degree used by qVFamTensorRationalDegree
(ArithmeticQPilotBaseChange.localResidueDegree) is the library relative
residue degree NumberFieldFinitePlace.relativeResidueDegree.  The two
constants have the same body; the equality is definitional. -/
theorem s2195_localResidueDegree_eq_relativeResidueDegree
    (place : NumberField.FinitePlace T.arithmetic.F) :
    ArithmeticQPilotBaseChange.localResidueDegree (k := ℚ) place =
      relativeResidueDegree (k := ℚ) place := rfl

/-- The local ramification index of the completed valuation rings is the
library relative ramification index. -/
theorem s2195_localRamificationIndex_eq_relativeRamificationIndex
    (place : NumberField.FinitePlace T.arithmetic.F) :
    localRamificationIndex (k := ℚ) place =
      relativeRamificationIndex (k := ℚ) place :=
  localRamificationIndex_eq_relativeRamificationIndex (k := ℚ) place

/-- The local inertia degree of the completed valuation rings is the library
relative residue degree. -/
theorem s2195_localInertiaDegree_eq_relativeResidueDegree
    (place : NumberField.FinitePlace T.arithmetic.F) :
    localInertiaDegree (k := ℚ) place =
      relativeResidueDegree (k := ℚ) place :=
  localInertiaDegree_eq_relativeResidueDegree (k := ℚ) place

/-- The actual tensor rational degree is the library relative residue degree at
the actual place. -/
theorem s2195_qVFamTensorRationalDegree_eq_relativeResidueDegree :
    qVFamTensorRationalDegree T b =
      relativeResidueDegree (k := ℚ) (qVFamTensorPlace T b) := rfl

/-- The S2040 degree-one condition is the library relative residue degree one. -/
theorem s2195_relativeResidueDegree_eq_one
    (hdeg : S2040QVPlaceDegreeOneRequired T b) :
    relativeResidueDegree (k := ℚ) (qVFamTensorPlace T b) = 1 :=
  hdeg

/-- The S2040 unramified condition, rewritten at the library relative
ramification index. -/
theorem s2195_relativeRamificationIndex_eq_one
    (hram : S2040QVPlaceUnramifiedRequired T b) :
    relativeRamificationIndex (k := ℚ) (qVFamTensorPlace T b) = 1 := by
  rw [← localRamificationIndex_eq_relativeRamificationIndex (k := ℚ) (qVFamTensorPlace T b)]
  exact hram

/-- The relative completion degree e * f at the actual place is one. -/
theorem s2195_relativeCompletionDegree_eq_one
    (hdeg : S2040QVPlaceDegreeOneRequired T b)
    (hram : S2040QVPlaceUnramifiedRequired T b) :
    relativeCompletionDegree (k := ℚ) (qVFamTensorPlace T b) = 1 := by
  rw [relativeCompletionDegree,
    s2195_relativeResidueDegree_eq_one T b hdeg,
    s2195_relativeRamificationIndex_eq_one T b hram, mul_one]

/-! ## 2. The construction required, proved unconditionally -/

/-- **The completion degree is one at the actual qVPlace**, from the two
arithmetic conditions only.  This is the finrank form of the S2040 layer (1)
arithmetic data, obtained from the unconditional local fundamental identity
finrank_adicCompletion_eq_relativeCompletionDegree_unconditional and the
instance alignments of Section 1. -/
theorem s2195_completionFinrankOne
    (hdeg : S2040QVPlaceDegreeOneRequired T b)
    (hram : S2040QVPlaceUnramifiedRequired T b) :
    Module.finrank
      ((comap (k := ℚ) (qVFamTensorPlace T b)).maximalIdeal.adicCompletion ℚ)
      ((qVFamTensorPlace T b).maximalIdeal.adicCompletion T.arithmetic.F) = 1 := by
  calc Module.finrank
        ((comap (k := ℚ) (qVFamTensorPlace T b)).maximalIdeal.adicCompletion ℚ)
        ((qVFamTensorPlace T b).maximalIdeal.adicCompletion T.arithmetic.F)
      = relativeCompletionDegree (k := ℚ) (qVFamTensorPlace T b) :=
        finrank_adicCompletion_eq_relativeCompletionDegree_unconditional
          (k := ℚ) (qVFamTensorPlace T b)
    _ = 1 := s2195_relativeCompletionDegree_eq_one T b hdeg hram

/-- **Instance alignment of the S2135 finrank type.**  The typed definition
S2135CompletionFinrankOne, elaborated in its own file, reads the canonical
completion algebra structure: its statement is definitionally the same finrank
form at which finrank_adicCompletion_eq_relativeCompletionDegree_unconditional
is stated in RelativeCompletionFinrankReduction. -/
theorem s2195_finrank_instance_alignment :
    S2135CompletionFinrankOne (l := l) T b ↔
      Module.finrank
        ((comap (k := ℚ) (qVFamTensorPlace T b)).maximalIdeal.adicCompletion ℚ)
        ((qVFamTensorPlace T b).maximalIdeal.adicCompletion T.arithmetic.F) = 1 :=
  Iff.rfl

/-- **The S2135 layer (1) construction requirement holds unconditionally.**  The
prime alignment hypothesis is not used for the finrank conclusion, so no
additional hypothesis beyond the two arithmetic conditions is introduced. -/
theorem s2195_layer1ConstructionRequired :
    S2135Layer1ConstructionRequired (l := l) T b := by
  intro _ hdeg hram
  show Module.finrank
      ((comap (k := ℚ) (qVFamTensorPlace T b)).maximalIdeal.adicCompletion ℚ)
      ((qVFamTensorPlace T b).maximalIdeal.adicCompletion T.arithmetic.F) = 1
  exact s2195_completionFinrankOne T b hdeg hram

/-! ## 3. From the completion degree one to the completion equivalence -/

/-- The actual completion embedding is surjective in degree one. -/
theorem s2195_completionMap_surjective
    (hfin : Module.finrank
      ((comap (k := ℚ) (qVFamTensorPlace T b)).maximalIdeal.adicCompletion ℚ)
      ((qVFamTensorPlace T b).maximalIdeal.adicCompletion T.arithmetic.F) = 1) :
    Function.Surjective (completionMap (k := ℚ) (qVFamTensorPlace T b)) := by
  intro w
  obtain ⟨c, hc⟩ :=
    exists_smul_eq_of_finrank_eq_one
      (K := (comap (k := ℚ) (qVFamTensorPlace T b)).maximalIdeal.adicCompletion ℚ)
      (V := (qVFamTensorPlace T b).maximalIdeal.adicCompletion T.arithmetic.F)
      hfin (x := (1 : (qVFamTensorPlace T b).maximalIdeal.adicCompletion T.arithmetic.F))
      one_ne_zero w
  refine ⟨c, ?_⟩
  rw [← algebraMap_instAlgebraAdicCompletion (k := ℚ) (qVFamTensorPlace T b)]
  exact (Algebra.algebraMap_eq_smul_one c).trans hc

/-- The degree-one completion embedding as a ring equivalence. -/
noncomputable def s2195_completionMapEquiv
    (hfin : Module.finrank
      ((comap (k := ℚ) (qVFamTensorPlace T b)).maximalIdeal.adicCompletion ℚ)
      ((qVFamTensorPlace T b).maximalIdeal.adicCompletion T.arithmetic.F) = 1) :
    ((comap (k := ℚ) (qVFamTensorPlace T b)).maximalIdeal.adicCompletion ℚ) ≃+*
      ((qVFamTensorPlace T b).maximalIdeal.adicCompletion T.arithmetic.F) :=
  RingEquiv.ofBijective (completionMap (k := ℚ) (qVFamTensorPlace T b))
    ⟨completionMap_injective (k := ℚ) (qVFamTensorPlace T b),
      s2195_completionMap_surjective T b hfin⟩

/-- The equivalence is the completion map on elements. -/
theorem s2195_completionMapEquiv_apply
    (hfin : Module.finrank
      ((comap (k := ℚ) (qVFamTensorPlace T b)).maximalIdeal.adicCompletion ℚ)
      ((qVFamTensorPlace T b).maximalIdeal.adicCompletion T.arithmetic.F) = 1)
    (x : (comap (k := ℚ) (qVFamTensorPlace T b)).maximalIdeal.adicCompletion ℚ) :
    s2195_completionMapEquiv T b hfin x =
      completionMap (k := ℚ) (qVFamTensorPlace T b) x := rfl

/-- Norm transport at degree one: the canonical completion norm of the image of
a nonzero element is the lower norm. -/
theorem s2195_norm_completionMap_eq
    (hfin : Module.finrank
      ((comap (k := ℚ) (qVFamTensorPlace T b)).maximalIdeal.adicCompletion ℚ)
      ((qVFamTensorPlace T b).maximalIdeal.adicCompletion T.arithmetic.F) = 1)
    (x : (comap (k := ℚ) (qVFamTensorPlace T b)).maximalIdeal.adicCompletion ℚ)
    (hx : x ≠ 0) :
    ‖completionMap (k := ℚ) (qVFamTensorPlace T b) x‖ = ‖x‖ := by
  have hpow := norm_completionMap_pow_of_finrank_eq_relativeCompletionDegree
    (k := ℚ) (qVFamTensorPlace T b) x hx
  calc ‖completionMap (k := ℚ) (qVFamTensorPlace T b) x‖
      = ‖x‖ ^ Module.finrank
          ((comap (k := ℚ) (qVFamTensorPlace T b)).maximalIdeal.adicCompletion ℚ)
          ((qVFamTensorPlace T b).maximalIdeal.adicCompletion T.arithmetic.F) := hpow
    _ = ‖x‖ ^ 1 := by
        exact congrArg (fun n => ‖x‖ ^ n) hfin
    _ = ‖x‖ := pow_one _

/-- The completion-map equivalence is isometric. -/
theorem s2195_completionMapEquiv_isometry
    (hfin : Module.finrank
      ((comap (k := ℚ) (qVFamTensorPlace T b)).maximalIdeal.adicCompletion ℚ)
      ((qVFamTensorPlace T b).maximalIdeal.adicCompletion T.arithmetic.F) = 1)
    (x : (comap (k := ℚ) (qVFamTensorPlace T b)).maximalIdeal.adicCompletion ℚ) :
    ‖s2195_completionMapEquiv T b hfin x‖ = ‖x‖ := by
  rw [s2195_completionMapEquiv_apply]
  by_cases hx : x = 0
  · rw [hx, map_zero, norm_zero, norm_zero]
  · exact s2195_norm_completionMap_eq T b hfin x hx

/-- The inverse direction is isometric as well. -/
theorem s2195_completionMapEquiv_symm_isometry
    (hfin : Module.finrank
      ((comap (k := ℚ) (qVFamTensorPlace T b)).maximalIdeal.adicCompletion ℚ)
      ((qVFamTensorPlace T b).maximalIdeal.adicCompletion T.arithmetic.F) = 1)
    (x : (qVFamTensorPlace T b).maximalIdeal.adicCompletion T.arithmetic.F) :
    ‖(s2195_completionMapEquiv T b hfin).symm x‖ = ‖x‖ := by
  have h := s2195_completionMapEquiv_isometry T b hfin
    ((s2195_completionMapEquiv T b hfin).symm x)
  rw [RingEquiv.apply_symm_apply] at h
  exact h.symm

/-! ## 4. The dependent cast at the rational place -/

/-- **The dependent cast.**  If the prime-strip place v has the same rational
prime as the actual qVPlace, then the contracted rational place is QPlace v.
This is the only place where the Fact (Nat.Prime v.1) instance is used; it is
provided by s2195FactPrime, so the S2046 abbreviation QPlace v elaborates
outside its defining file. -/
theorem s2195_comap_eq_QPlace
    (v : FinitePrimePlace 2 7) (hv : v.1 = qVFamTensorP T b) :
    comap (k := ℚ) (qVFamTensorPlace T b) = QPlace v := by
  have h := comap_eq_rationalFinitePlace (K := T.arithmetic.F) (p := v.1)
    (⟨qVFamTensorPlace T b, hv.symm⟩ : FinitePlaceAtPrime T.arithmetic.F v.1)
  unfold QPlace
  rw [h]
  rfl

/-- The type cast between the two rational completions along the dependent
place equality. -/
noncomputable def s2195_placeCast
    (q : NumberField.FinitePlace ℚ)
    (hq : comap (k := ℚ) (qVFamTensorPlace T b) = q) :
    ((comap (k := ℚ) (qVFamTensorPlace T b)).maximalIdeal.adicCompletion ℚ) ≃+*
      Completion q :=
  hq ▸ RingEquiv.refl
    ((comap (k := ℚ) (qVFamTensorPlace T b)).maximalIdeal.adicCompletion ℚ)

/-- The dependent place cast is isometric. -/
theorem s2195_placeCast_isometry
    (q : NumberField.FinitePlace ℚ)
    (hq : comap (k := ℚ) (qVFamTensorPlace T b) = q)
    (y : (comap (k := ℚ) (qVFamTensorPlace T b)).maximalIdeal.adicCompletion ℚ) :
    ‖s2195_placeCast T b q hq y‖ = ‖y‖ := by
  cases hq
  rfl

/-- **The transported layer (1) split equivalence.**  For any rational place q
equal to the contraction of the actual qVPlace, the degree-one completion
embedding composes with the dependent cast to give a ring equivalence from
Completion (qVPlace T b) to Completion q. -/
noncomputable def s2195_completionEquivOfPlace
    (q : NumberField.FinitePlace ℚ)
    (hq : comap (k := ℚ) (qVFamTensorPlace T b) = q)
    (hfin : Module.finrank
      ((comap (k := ℚ) (qVFamTensorPlace T b)).maximalIdeal.adicCompletion ℚ)
      ((qVFamTensorPlace T b).maximalIdeal.adicCompletion T.arithmetic.F) = 1) :
    Completion (qVPlace (l := l) T b) ≃+* Completion q :=
  (s2195_completionMapEquiv T b hfin).symm.trans (s2195_placeCast T b q hq)

/-- The transported split equivalence is isometric. -/
theorem s2195_completionEquivOfPlace_isometry
    (q : NumberField.FinitePlace ℚ)
    (hq : comap (k := ℚ) (qVFamTensorPlace T b) = q)
    (hfin : Module.finrank
      ((comap (k := ℚ) (qVFamTensorPlace T b)).maximalIdeal.adicCompletion ℚ)
      ((qVFamTensorPlace T b).maximalIdeal.adicCompletion T.arithmetic.F) = 1)
    (x : Completion (qVPlace (l := l) T b)) :
    ‖s2195_completionEquivOfPlace T b q hq hfin x‖ = ‖x‖ := by
  rw [show s2195_completionEquivOfPlace T b q hq hfin x =
      s2195_placeCast T b q hq
        ((s2195_completionMapEquiv T b hfin).symm x) from rfl]
  rw [s2195_placeCast_isometry, s2195_completionMapEquiv_symm_isometry]

/-! ## 5. The aligned split datum and package -/

/-- **The aligned split datum**: the rational place v is at the actual
rational prime qVFamTensorP T b, and the completion equivalence to QPlace v
is constructed from the degree-one identity. -/
noncomputable def s2195_primeAlignedSplitData
    (v : FinitePrimePlace 2 7) (hv : v.1 = qVFamTensorP T b)
    (hdeg : S2040QVPlaceDegreeOneRequired T b)
    (hram : S2040QVPlaceUnramifiedRequired T b) :
    S2135PrimeAlignedSplitData T b where
  data :=
    { v := v
      completionEquiv :=
        s2195_completionEquivOfPlace T b (QPlace v)
          (s2195_comap_eq_QPlace T b v hv)
          (s2195_completionFinrankOne T b hdeg hram)
      completion_isometry := fun x =>
        s2195_completionEquivOfPlace_isometry T b (QPlace v)
          (s2195_comap_eq_QPlace T b v hv)
          (s2195_completionFinrankOne T b hdeg hram) x }
  prime_eq := hv

/-- **The aligned full split package**, constructed from the prime alignment
and the two arithmetic conditions. -/
noncomputable def s2195_primeAlignedSplitPackage
    (v : FinitePrimePlace 2 7) (hv : v.1 = qVFamTensorP T b)
    (hdeg : S2040QVPlaceDegreeOneRequired T b)
    (hram : S2040QVPlaceUnramifiedRequired T b) :
    S2135PrimeAlignedSplitPackage T b where
  data := (s2195_primeAlignedSplitData T b v hv hdeg hram).data
  prime_eq := hv
  degree_one := hdeg
  unramified := hram

/-- **Existence criterion.**  The aligned split package exists whenever the
actual rational prime lies in the paper prime strip 2..7; the pair of
arithmetic conditions is the other input. -/
theorem s2195_exists_primeAlignedSplitPackage
    (hmem : qVFamTensorP T b ∈ primeStrip 2 7)
    (hdeg : S2040QVPlaceDegreeOneRequired T b)
    (hram : S2040QVPlaceUnramifiedRequired T b) :
    ∃ P : S2135PrimeAlignedSplitPackage T b,
      P.data.v.1 = qVFamTensorP T b :=
  ⟨s2195_primeAlignedSplitPackage T b ⟨qVFamTensorP T b, hmem⟩ rfl hdeg hram, rfl⟩

/-- The converse obstruction, imported from S2135: a rational prime outside the
paper prime strip admits no aligned split package.  This is the exact first
missing input at an arbitrary (T, b). -/
theorem s2195_no_primeAlignedSplitPackage_of_not_mem
    (h : qVFamTensorP T b ∉ primeStrip 2 7) :
    IsEmpty (S2135PrimeAlignedSplitPackage T b) :=
  s2135_no_aligned_package_of_prime_not_mem T b h

/-- **The exact first missing input.**  Once the two arithmetic conditions hold,
the existence of the aligned split package is equivalent to the rational prime
of the actual qVPlace lying in the paper prime strip: the rational place is
forced by the package, and the package is constructed from the membership.  The
source b supplies neither the membership nor the two arithmetic conditions. -/
theorem s2195_nonempty_primeAlignedSplitPackage_iff
    (hdeg : S2040QVPlaceDegreeOneRequired T b)
    (hram : S2040QVPlaceUnramifiedRequired T b) :
    Nonempty (S2135PrimeAlignedSplitPackage T b) ↔
      S2135PrimeAlignmentRequired (l := l) T b := by
  unfold S2135PrimeAlignmentRequired
  constructor
  · rintro ⟨P⟩
    rw [← P.prime_eq]
    exact P.data.v.2
  · intro hmem
    exact ⟨s2195_primeAlignedSplitPackage T b ⟨qVFamTensorP T b, hmem⟩ rfl hdeg hram⟩

/-- The constructed package is an S2040 split package. -/
noncomputable def s2195_toPackage
    (v : FinitePrimePlace 2 7) (hv : v.1 = qVFamTensorP T b)
    (hdeg : S2040QVPlaceDegreeOneRequired T b)
    (hram : S2040QVPlaceUnramifiedRequired T b) :
    S2040QVPlaceSplitPackage T b :=
  s2135_toPackage T b (s2195_primeAlignedSplitPackage T b v hv hdeg hram)

/-! ## 6. Axiom probes -/

#print axioms s2195_localResidueDegree_eq_relativeResidueDegree
#print axioms s2195_localRamificationIndex_eq_relativeRamificationIndex
#print axioms s2195_localInertiaDegree_eq_relativeResidueDegree
#print axioms s2195_relativeCompletionDegree_eq_one
#print axioms s2195_completionFinrankOne
#print axioms s2195_layer1ConstructionRequired
#print axioms s2195_completionMap_surjective
#print axioms s2195_completionMapEquiv_isometry
#print axioms s2195_comap_eq_QPlace
#print axioms s2195_placeCast_isometry
#print axioms s2195_completionEquivOfPlace_isometry
#print axioms s2195_exists_primeAlignedSplitPackage
#print axioms s2195_finrank_instance_alignment
#print axioms s2195_nonempty_primeAlignedSplitPackage_iff
#print axioms s2195_completionMapEquiv
#print axioms s2195_completionEquivOfPlace
#print axioms s2195_primeAlignedSplitPackage
#print axioms s2195_toPackage
#check S2135Layer1ConstructionRequired
#check s2195_layer1ConstructionRequired
#check s2195_completionEquivOfPlace
#check s2195_primeAlignedSplitPackage

end LeanFormal.IUT.XiFPaper.S2195Layer1InstanceActual
end
