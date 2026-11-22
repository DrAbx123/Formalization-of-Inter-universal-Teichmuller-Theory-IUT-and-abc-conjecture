import tmp.sheaf.xif.paper.S2706DirectHcompActual
import tmp.sheaf.xif.paper.S2708MultiQSourcePilotActual
import tmp.sheaf.xif.paper.S2703GaussianPrimePlacesActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange

/-!
# S2709: the actual multi-q bad-place family over the paper source datum

This file connects the multi-q compatibility layer of
S2708MultiQSourcePilotActual to the actual paper source datum of
S2706DirectHcompActual / S2704S2696SourceDataActual.

The bad-place index is the actual source index
Bad (S2696SelectionTwo l) (the paper set {5, 2161}); the place map is the
section lift sectionFiniteLift used by the source; the q-candidate family is
the actual completed-DVR badPlaceQCandidate of the source.  The multi-q
log-volume is the actual source scalar sourceBadQAbsLog.

The only arithmetic input beyond the definitional source bridge is the
residue-norm computation at the two actual places:
residueNormBase = residueCharacteristic at the concrete five place
(S1487) and at the Gaussian place above 2161.  The latter is proved here from
the explicit split Gaussian primes 44 +- 15i (S2703): every prime over
(2161) contains the product (44+15i)(44-15i), hence is one of the two explicit
maximal ideals, whose absolute norm is 2161.

## Main results

* S2709Q: the actual MultiQSourcePilotData with index
  Bad (S2696SelectionTwo l), place = sectionFiniteLift,
  q = badPlaceQCandidate, and logVolume = sourceBadQAbsLog.
* S2709_multiQLogVolume_eq_sourceBadQAbsLog and
  S2709_multiQLogVolume_eq_badPlace_sum.
* S2709_hq_multi: the multi-q replacement of the single-q target,
  sourceQPilotSignedLog = multiQPaperQPilotLogVolume.
* S2709_multiQPaperQPilotObject_qPilotLogVolume_eq_source and its
  sourceBadQAbsLog version.

No sorry, axiom, native_decide or True is used.
-/

noncomputable section
open scoped BigOperators

set_option maxRecDepth 100000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2709MultiQHqActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S2696VbadActual
open LeanFormal.IUT.XiFPaper.S2704S2696SourceDataActual
open LeanFormal.IUT.XiFPaper.S2706DirectHcompActual
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual
open LeanFormal.IUT.XiFPaper.S2703GaussianPrimePlacesActual
open LeanFormal.IUT.XiFPaper.S2708MultiQSourcePilotActual

local instance s2709GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

universe uL uC uG

/-! ## 1. Real logarithm of an inverted power -/

/-- The absolute log of N^{-n} is n log N for N > 1. -/
theorem abs_log_inv_pow_eq {N : ℝ} (hN : 1 < N) (n : ℕ) :
    |Real.log (N⁻¹ ^ n)| = (n : ℝ) * Real.log N := by
  have hlog : 0 < Real.log N := Real.log_pos hN
  rw [Real.log_pow, Real.log_inv]
  rw [show (n : ℝ) * -Real.log N = -((n : ℝ) * Real.log N) by ring]
  rw [abs_neg, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg n) (le_of_lt hlog))]

/-- A finite-place residue characteristic is at least 2, hence its real cast is
strictly bigger than 1. -/
theorem one_lt_residueCharacteristic_cast (p : NumberField.FinitePlace GaussianField) :
    (1 : ℝ) < (NumberFieldFinitePlace.residueCharacteristic p : ℝ) := by
  exact_mod_cast (NumberFieldFinitePlace.residueCharacteristic_prime p).one_lt

/-! ## 2. The two explicit Gaussian primes over 2161 -/

/-- The absolute norm of the transported prime (44+15i) is 2161. -/
theorem gaussianField2161PrimePlus_absNorm_actual :
    Ideal.absNorm gaussianField2161PrimePlus = 2161 := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  calc Nat.card (gaussianO ⧸ gaussianField2161PrimePlus)
      = Nat.card (ZMod 2161) :=
        Nat.card_congr gaussianField2161PrimePlusResidueEquiv.toEquiv
    _ = 2161 := Nat.card_zmod 2161

/-- The absolute norm of the transported prime (44-15i) is 2161. -/
theorem gaussianField2161PrimeMinus_absNorm_actual :
    Ideal.absNorm gaussianField2161PrimeMinus = 2161 := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  calc Nat.card (gaussianO ⧸ gaussianField2161PrimeMinus)
      = Nat.card (ZMod 2161) :=
        Nat.card_congr gaussianField2161PrimeMinusResidueEquiv.toEquiv
    _ = 2161 := Nat.card_zmod 2161

/-- The product of the two explicit primes over 2161 is the principal ideal
(2161) in the Gaussian ring of integers. -/
theorem gaussianField2161PrimePlus_mul_minus_eq_span :
    gaussianField2161PrimePlus * gaussianField2161PrimeMinus =
      Ideal.span {(2161 : NumberField.RingOfIntegers GaussianField)} := by
  have hmap_inj : Function.Injective
      (Ideal.map gaussianRingOfIntegersEquivGaussianInt.toRingHom) := by
    intro I J h
    have h' := congrArg
      (Ideal.comap gaussianRingOfIntegersEquivGaussianInt.toRingHom) h
    rw [Ideal.comap_map_of_bijective
          (f := gaussianRingOfIntegersEquivGaussianInt.toRingHom)
          gaussianRingOfIntegersEquivGaussianInt.bijective,
        Ideal.comap_map_of_bijective
          (f := gaussianRingOfIntegersEquivGaussianInt.toRingHom)
          gaussianRingOfIntegersEquivGaussianInt.bijective] at h'
    exact h'
  apply hmap_inj
  rw [Ideal.map_mul]
  have hP : Ideal.map gaussianRingOfIntegersEquivGaussianInt.toRingHom
      gaussianField2161PrimePlus = Ideal.span {piPlus} := by
    rw [gaussianField2161PrimePlus,
      Ideal.map_comap_of_surjective gaussianRingOfIntegersEquivGaussianInt.toRingHom
        gaussianRingOfIntegersEquivGaussianInt.surjective]
  have hM : Ideal.map gaussianRingOfIntegersEquivGaussianInt.toRingHom
      gaussianField2161PrimeMinus = Ideal.span {piMinus} := by
    rw [gaussianField2161PrimeMinus,
      Ideal.map_comap_of_surjective gaussianRingOfIntegersEquivGaussianInt.toRingHom
        gaussianRingOfIntegersEquivGaussianInt.surjective]
  rw [hP, hM]
  have hcast : gaussianRingOfIntegersEquivGaussianInt.toRingHom
      (2161 : NumberField.RingOfIntegers GaussianField) = (2161 : GaussianInt) :=
    map_natCast _ 2161
  rw [Ideal.map_span, Set.image_singleton, hcast]
  rw [Ideal.span_singleton_mul_span_singleton, piPlus_mul_piMinus]

/-- 2161 lies in the maximal ideal of the S2696 Gaussian place above 2161. -/
theorem S2696GaussianPlace2161_mem_maximalIdeal :
    (2161 : NumberField.RingOfIntegers GaussianField) ∈
      S2696GaussianPlace2161.maximalIdeal.asIdeal := by
  have hunder := NumberFieldFinitePlace.under_eq_span_residueCharacteristic
    (S2696GaussianPlace2161)
  have hmem : (2161 : ℤ) ∈
      S2696GaussianPlace2161.maximalIdeal.asIdeal.under ℤ := by
    rw [hunder, S2696GaussianPlace2161_residueCharacteristic]
    exact Ideal.mem_span_singleton_self _
  have hmem' : algebraMap ℤ (NumberField.RingOfIntegers GaussianField) (2161 : ℤ) ∈
      S2696GaussianPlace2161.maximalIdeal.asIdeal := by
    have h := hmem
    rw [Ideal.under_def, Ideal.mem_comap] at h
    exact h
  simpa using hmem'

/-- Every prime of the Gaussian integers over 2161 is one of the two explicit
split primes. -/
theorem S2696GaussianPlace2161_maximalIdeal_eq_plus_or_minus :
    S2696GaussianPlace2161.maximalIdeal.asIdeal = gaussianField2161PrimePlus ∨
      S2696GaussianPlace2161.maximalIdeal.asIdeal = gaussianField2161PrimeMinus := by
  have hPprime : (S2696GaussianPlace2161.maximalIdeal.asIdeal).IsPrime :=
    S2696GaussianPlace2161.maximalIdeal.isPrime
  have hPne : S2696GaussianPlace2161.maximalIdeal.asIdeal ≠ ⊤ := hPprime.ne_top
  have hmem := S2696GaussianPlace2161_mem_maximalIdeal
  have hspan : Ideal.span {(2161 : NumberField.RingOfIntegers GaussianField)} ≤
      S2696GaussianPlace2161.maximalIdeal.asIdeal :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmem)
  have hle : gaussianField2161PrimePlus * gaussianField2161PrimeMinus ≤
      S2696GaussianPlace2161.maximalIdeal.asIdeal := by
    rw [gaussianField2161PrimePlus_mul_minus_eq_span]
    exact hspan
  rcases (hPprime.mul_le).mp hle with hplus | hminus
  · left
    exact (gaussianField2161PrimePlus_isMaximal.eq_of_le hPne hplus).symm
  · right
    exact (gaussianField2161PrimeMinus_isMaximal.eq_of_le hPne hminus).symm

/-- The arithmetic residue norm base at the S2696 Gaussian place above 2161 is
2161 (residue degree one from the explicit splitting). -/
theorem residueNormBase_S2696GaussianPlace2161 :
    residueNormBase S2696GaussianPlace2161 = 2161 := by
  unfold residueNormBase
  rcases S2696GaussianPlace2161_maximalIdeal_eq_plus_or_minus with h | h
  · rw [h, gaussianField2161PrimePlus_absNorm_actual]
    norm_num
  · rw [h, gaussianField2161PrimeMinus_absNorm_actual]
    norm_num

/-! ## 3. The section lift of a bad moduli place is the place itself -/

/-- On the concrete identity tower Fmod = F = K = Q(i), the section lift of a
bad moduli place is the place itself. -/
theorem sectionFiniteLift_eq_self (l : PrimeGeFive)
    (p : NumberField.FinitePlace GaussianField) :
    sectionFiniteLift (S2696SelectionTwo l) p = p := by
  have h1 : NumberFieldFinitePlace.comap (k := (S1280Arithmetic l).Fmod)
      (sectionFiniteLift (S2696SelectionTwo l) p) =
      sectionFiniteLift (S2696SelectionTwo l) p :=
    S1280_comap_eq_self l (sectionFiniteLift (S2696SelectionTwo l) p)
  have h2 : NumberFieldFinitePlace.comap (k := (S1280Arithmetic l).Fmod)
      (sectionFiniteLift (S2696SelectionTwo l) p) = p :=
    sectionFiniteLift_comap (S2696SelectionTwo l) p
  exact h1.symm.trans h2

/-- The residue norm base pinned to the concrete Gaussian field, avoiding the
definitionally equal but differently instantiated field presentation K. -/
noncomputable def canonicalResidueNormBase
    (p : NumberField.FinitePlace GaussianField) : ℝ :=
  residueNormBase p

/-- The residue norm base of the section lift of an actual bad moduli place is
its residue characteristic. -/
theorem residueNormBase_sectionFiniteLift_eq_residueCharacteristic
    (l : PrimeGeFive) (b : Bad (S2696SelectionTwo l)) :
    residueNormBase (sectionFiniteLift (S2696SelectionTwo l) b.1) =
      (NumberFieldFinitePlace.residueCharacteristic b.1 : ℝ) := by
  obtain ⟨p, hp⟩ := b
  change residueNormBase (sectionFiniteLift (S2696SelectionTwo l) p) =
    (NumberFieldFinitePlace.residueCharacteristic p : ℝ)
  have hcomap : NumberFieldFinitePlace.comap (k := (S1280Arithmetic l).Fmod) p =
      p :=
    S1280_comap_eq_self l p
  have hmem : NumberFieldFinitePlace.comap (k := (S1280Arithmetic l).Fmod) p ∈
      (S2696SelectionTwo l).V_mod_bad := by
    rw [hcomap]
    exact hp
  have hp' := S2696_bad_fibre_eq l p hmem
  rcases hp' with rfl | rfl
  · have hcanon : canonicalResidueNormBase (sectionFiniteLift (S2696SelectionTwo l)
        (concreteGaussianFivePlace : NumberField.FinitePlace GaussianField)) =
        (NumberFieldFinitePlace.residueCharacteristic
          (concreteGaussianFivePlace : NumberField.FinitePlace GaussianField) : ℝ) := by
      unfold canonicalResidueNormBase
      rw [sectionFiniteLift_eq_self,
        concreteGaussianFivePlace_residueCharacteristic]
      exact S1487_residueNormBase_five
    exact hcanon
  · have hcanon : canonicalResidueNormBase (sectionFiniteLift (S2696SelectionTwo l)
        (S2696GaussianPlace2161 : NumberField.FinitePlace GaussianField)) =
        (NumberFieldFinitePlace.residueCharacteristic
          (S2696GaussianPlace2161 : NumberField.FinitePlace GaussianField) : ℝ) := by
      unfold canonicalResidueNormBase
      rw [sectionFiniteLift_eq_self,
        S2696GaussianPlace2161_residueCharacteristic,
        residueNormBase_S2696GaussianPlace2161]
      norm_num
    exact hcanon

/-! ## 4. The actual per-place magnitude identity -/

/-- At every actual bad index, the local log magnitude of the source
badPlaceQCandidate equals the source |log q_b| computed from
badPlaceQProxy.  The place equality is kept as the explicit hypothesis hres;
the residue-norm case split is done separately below. -/
theorem localLogMagnitude_badPlaceQCandidate_eq_abs_log_badPlaceQProxy_of_res
    (l : PrimeGeFive)
    (p : NumberField.FinitePlace (S1280Arithmetic l).Fmod)
    (hp : p ∈ (S2696SelectionTwo l).V_mod_bad)
    (hres : residueNormBase (sectionFiniteLift (S2696SelectionTwo l) p) =
      (NumberFieldFinitePlace.residueCharacteristic p : ℝ)) :
    localLogMagnitude (badPlaceQCandidate (S2696SelectionTwo l) ⟨p, hp⟩) =
      |Real.log (badPlaceQProxy (S2696SelectionTwo l) ⟨p, hp⟩)| := by
  have hN : (1 : ℝ) < (NumberFieldFinitePlace.residueCharacteristic p : ℝ) :=
    one_lt_residueCharacteristic_cast p
  rw [localLogMagnitude_eq_order_mul_log, hres, badPlaceQProxy]
  simp only [Subtype.coe_mk]
  rw [abs_log_inv_pow_eq (N := (NumberFieldFinitePlace.residueCharacteristic p : ℝ)) hN]

/-- At every actual bad index, the local log magnitude of the source
badPlaceQCandidate equals the source |log q_b| computed from
badPlaceQProxy. -/
theorem localLogMagnitude_badPlaceQCandidate_eq_abs_log_badPlaceQProxy
    (l : PrimeGeFive) (b : Bad (S2696SelectionTwo l)) :
    localLogMagnitude (badPlaceQCandidate (S2696SelectionTwo l) b) =
      |Real.log (badPlaceQProxy (S2696SelectionTwo l) b)| :=
  localLogMagnitude_badPlaceQCandidate_eq_abs_log_badPlaceQProxy_of_res
    l b.1 b.2 (residueNormBase_sectionFiniteLift_eq_residueCharacteristic l b)

/-! ## 5. The actual multi-q source datum -/

/-- The actual multi-q family over the paper bad places {5, 2161}.

* the index is the actual source bad-moduli index Bad (S2696SelectionTwo l);
* the place of a bad index is the source section lift (which is the place itself
  on the concrete identity tower);
* the q-candidate is the actual completed-DVR badPlaceQCandidate of the source;
* the log-volume is the actual source scalar sourceBadQAbsLog. -/
noncomputable def S2709Q
    {l : PrimeGeFive}
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    MultiQSourcePilotData (I := S2706I R redCompat hredCompat torCompat htorCompat
      orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat) where
  index := Bad (S2696SelectionTwo l)
  fintype := S2696BadFintype l
  place := fun b => sectionFiniteLift (S2696SelectionTwo l) b.1
  q := fun b => badPlaceQCandidate (S2696SelectionTwo l) b
  logVolume := sourceBadQAbsLog (S2706SourceData R redCompat hredCompat torCompat
    htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)
  logVolume_eq := by
    letI : Fintype (Bad (S2696SelectionTwo l)) := S2696BadFintype l
    have hsrc : sourceBadQAbsLog (S2706SourceData R redCompat hredCompat torCompat
        htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat) =
        ∑ b : Bad (S2696SelectionTwo l),
          |Real.log (badPlaceQProxy (S2696SelectionTwo l) b)| :=
      S2696SourceData_sourceBadQAbsLog_eq_sum l R redCompat hredCompat torCompat
        htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat
    rw [hsrc]
    exact Finset.sum_congr rfl (fun b _ =>
      (localLogMagnitude_badPlaceQCandidate_eq_abs_log_badPlaceQProxy l b).symm)
  logVolume_eq_source := rfl

/-! ## 6. The multi-q replacement of the single-q target -/

/-- The multi-q log-volume of the actual source family is the actual source
bad-q absolute log. -/
theorem S2709_multiQLogVolume_eq_sourceBadQAbsLog
    {l : PrimeGeFive}
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    multiQLogVolume (S2709Q R redCompat hredCompat torCompat htorCompat
      orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat) =
      sourceBadQAbsLog (S2706SourceData R redCompat hredCompat torCompat htorCompat
        orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat) :=
  multiQLogVolume_eq_sourceBadQAbsLog
    (S2709Q R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
      secCompat hsecCompat cusCompat hcusCompat)

/-- The multi-q log-volume is the actual per-place sum over Bad
(S2696SelectionTwo l) of |log q_b|. -/
theorem S2709_multiQLogVolume_eq_badPlace_sum
    {l : PrimeGeFive}
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    multiQLogVolume (S2709Q R redCompat hredCompat torCompat htorCompat
      orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat) =
      ∑ b : Bad (S2696SelectionTwo l),
        |Real.log (badPlaceQProxy (S2696SelectionTwo l) b)| := by
  rw [S2709_multiQLogVolume_eq_sourceBadQAbsLog]
  exact S2696SourceData_sourceBadQAbsLog_eq_sum l R redCompat hredCompat torCompat
    htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat

/-- **The hq replacement.**  The source signed q-pilot log of the paper datum
is the multi-q paper q-pilot log-volume of the actual bad-place family.  This
replaces the single-q target by the definitional multi-q equality proved in
S2708, instantiated at the actual S2696 bad family. -/
theorem S2709_hq_multi
    {l : PrimeGeFive}
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    sourceQPilotSignedLog (S2706SourceData R redCompat hredCompat torCompat htorCompat
      orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat) =
      multiQPaperQPilotLogVolume (S2709Q R redCompat hredCompat torCompat htorCompat
        orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat) :=
  (multiQPaperQPilotLogVolume_eq_sourceQPilotSignedLog
    (S2709Q R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
      secCompat hsecCompat cusCompat hcusCompat)).symm

/-- The same replacement with the literal initial-field presentation
(S2706I ...).initial. -/
theorem S2709_hq_multi_initial
    {l : PrimeGeFive}
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    sourceQPilotSignedLog (S2706I R redCompat hredCompat torCompat htorCompat
      orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat).initial =
      multiQPaperQPilotLogVolume (S2709Q R redCompat hredCompat torCompat htorCompat
        orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat) :=
  S2709_hq_multi R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
    secCompat hsecCompat cusCompat hcusCompat

/-- The multi-q paper q-pilot log-volume is minus the actual per-place bad-q sum. -/
theorem S2709_multiQPaperQPilotLogVolume_eq_badPlace_sum
    {l : PrimeGeFive}
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    multiQPaperQPilotLogVolume (S2709Q R redCompat hredCompat torCompat htorCompat
      orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat) =
      -∑ b : Bad (S2696SelectionTwo l),
        |Real.log (badPlaceQProxy (S2696SelectionTwo l) b)| := by
  unfold multiQPaperQPilotLogVolume
  rw [S2709_multiQLogVolume_eq_badPlace_sum]

/-- The q-pilot log-volume of the multi-q paper q-pilot object is the actual
source bad-q absolute log. -/
theorem S2709_multiQPaperQPilotObject_qPilotLogVolume_eq_sourceBadQAbsLog
    {l : PrimeGeFive}
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat)
    {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
    {G : Type uG} [Group G] [TopologicalSpace G]
    {envStrip : FPrimeStrip (FinitePrimePlace 2 7)}
    (O : PaperQPilotObject (l := l) (V := FinitePrimePlace 2 7)
      (Label := Label) (Choice := Choice)
      (S2706I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
        secCompat hsecCompat cusCompat hcusCompat) G envStrip) :
    (multiQPaperQPilotObject O (S2709Q R redCompat hredCompat torCompat htorCompat
      orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)).qPilotLogVolume =
      -sourceBadQAbsLog (S2706SourceData R redCompat hredCompat torCompat htorCompat
        orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat) :=
  multiQPaperQPilotObject_qPilotLogVolume O
    (S2709Q R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
      secCompat hsecCompat cusCompat hcusCompat)

/-- The q-pilot log-volume of the multi-q paper q-pilot object is the source
signed q-pilot log. -/
theorem S2709_multiQPaperQPilotObject_qPilotLogVolume_eq_source
    {l : PrimeGeFive}
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat)
    {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
    {G : Type uG} [Group G] [TopologicalSpace G]
    {envStrip : FPrimeStrip (FinitePrimePlace 2 7)}
    (O : PaperQPilotObject (l := l) (V := FinitePrimePlace 2 7)
      (Label := Label) (Choice := Choice)
      (S2706I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
        secCompat hsecCompat cusCompat hcusCompat) G envStrip) :
    (multiQPaperQPilotObject O (S2709Q R redCompat hredCompat torCompat htorCompat
      orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)).qPilotLogVolume =
      sourceQPilotSignedLog (S2706SourceData R redCompat hredCompat torCompat htorCompat
        orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat) := by
  rw [multiQPaperQPilotObject_qPilotLogVolume]
  rfl

/-! ## 7. Audit -/

#check S2709Q
#check S2709_multiQLogVolume_eq_sourceBadQAbsLog
#check S2709_multiQLogVolume_eq_badPlace_sum
#check S2709_hq_multi
#check S2709_hq_multi_initial
#check S2709_multiQPaperQPilotLogVolume_eq_badPlace_sum
#check S2709_multiQPaperQPilotObject_qPilotLogVolume_eq_sourceBadQAbsLog
#check S2709_multiQPaperQPilotObject_qPilotLogVolume_eq_source
#print axioms S2709Q
#print axioms residueNormBase_S2696GaussianPlace2161
#print axioms localLogMagnitude_badPlaceQCandidate_eq_abs_log_badPlaceQProxy
#print axioms S2709_multiQLogVolume_eq_sourceBadQAbsLog
#print axioms S2709_hq_multi
#print axioms S2709_hq_multi_initial
#print axioms S2709_multiQPaperQPilotObject_qPilotLogVolume_eq_source

end LeanFormal.IUT.XiFPaper.S2709MultiQHqActual
end
