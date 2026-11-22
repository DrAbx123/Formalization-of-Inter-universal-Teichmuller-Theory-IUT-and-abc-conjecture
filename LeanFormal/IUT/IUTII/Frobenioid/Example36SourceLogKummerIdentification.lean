import LeanFormal.IUT.IUTII.Frobenioid.Example36LogDomainActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36LogKummerMap
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceTheaterCarrier
import LeanFormal.IUT.IUTII.Frobenioid.Example36GaussianSplitPlaceArithmetic
import LeanFormal.IUT.IUTII.Frobenioid.ConcreteSourceFrobenioidBridge

/-!
# Layer1 F6/F7: independent source log-Kummer/Frobenius carrier over Q_l

Route (b) of the task-108 decision: the source principal units, log-Kummer map,
log-shell, Frobenius and p-fold scaling are constructed INDEPENDENTLY on the
actual source local field Q_l (the local field of the source theater's actual
Tate local carrier, q = l in Q_l), using the tree's actual principal-unit log
and log-shell theorems.  No refl comparison to the concrete Gaussian-completion
data is used.

Actual formulas (source side):
* source local field = Q_l;
* source principal units H_l = principalUnits (K := Q_l) = 1 + m_l;
* source log-Kummer map u |-> principalUnitLog u (tree's log1p on u - 1);
* source log-shell L_l = principalUnitLogImage (K := Q_l) l;
* source Frobenius u |-> u^l on H_l;
* source p-fold scaling x |-> l * x on L_l, membership from log(u^l) = l log(u);
* commutation proved from the actual power law;
* nontriviality proved from the actual sharp inverse ball (the uniformizer l is
  in the sharp ball for l >= 5, hence in the log-shell, and l*x differs from x).

The source carrier card SourceFrobeniusLogKummerCard l is actually inhabited by
this Q_l construction.  At l = 5 the FIELD-level Q_5 comparison with the
concrete Gaussian completion is constructed below: the lower completion
Completion (comap concretePlace) has rational prime 5 and completionMap is a
ring equivalence onto Completion concretePlace because the completion degree
is one.  This is the field comparison plus the integer-unit and principal-unit carrier
transport (concretePlace_integersRingEquiv, concretePlace_unitsEquiv,
concretePlace_principalUnitsEquiv), using the isometry of completionMap.
It is not yet the full log-shell/log-Kummer identification: the analytic
compatibility of the principal-unit logarithm with this comparison (needed for
the shell equivalence) and the scaled log-Kummer map/p-scaling intertwiners
(the tree log-Kummer is scaled by logShellScale, the independent Q_l source
log-Kummer is unscaled) remain the exact content of
SourceFrobeniusLogKummerIdentificationCard.  For general l the place models
differ; the remaining identification card is recorded and not inhabited.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid.Example36

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.IUTII.Frobenioid.Example36.LogShellLattice
open LeanFormal.IUT.IUTII.Frobenioid.Example36.LogShellFrobeniusAction
open LeanFormal.IUT.IUTII.Frobenioid.Example36.LogKummerMap
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceTheaterCarrier
open scoped NumberField

local instance sourceLogKummerGaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance sourceLogKummerFivePrime : Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

local instance sourceLogKummerPrimeFactAll (l : PrimeGeFive) :
    Fact (Nat.Prime l.value) :=
  l.factPrime

/-! ## 1. The actual power law for the tree principal-unit logarithm -/

section LogarithmPower

variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
variable [IsUltrametricDist K] [ProperSpace K]

theorem principalUnitLog_pow (p : ℕ) [Fact p.Prime]
    [NormedAlgebra ℚ_[p] K] (n : ℕ) (u : principalUnits (K := K)) :
    principalUnitLog (K := K) (u ^ n) = (n : K) * principalUnitLog (K := K) u := by
  induction n with
  | zero => rw [pow_zero, principalUnitLog_one, Nat.cast_zero, zero_mul]
  | succ n ih =>
      rw [pow_succ, principalUnitLog_mul (K := K) p, ih]
      push_cast
      rw [add_mul, one_mul]

end LogarithmPower

/-! ## 2. The independent source carrier over Q_l -/

section SourceOverQl

variable (l : PrimeGeFive)

abbrev sourceLocalField : Type := ℚ_[l.value]
abbrev sourcePrincipalUnits : Type := principalUnits (K := sourceLocalField l)

def sourceLogKummer (u : sourcePrincipalUnits l) : sourceLocalField l :=
  principalUnitLog (K := sourceLocalField l) u

noncomputable def sourceFrobenius (u : sourcePrincipalUnits l) :
    sourcePrincipalUnits l :=
  ⟨(u : (Integers (sourceLocalField l))ˣ) ^ l.value,
    (principalUnits (K := sourceLocalField l)).pow_mem u.property l.value⟩

noncomputable def sourceLogShell : AddSubgroup (sourceLocalField l) :=
  principalUnitLogImage (K := sourceLocalField l) l.value

def sourceLogKummerShell (u : sourcePrincipalUnits l) : sourceLogShell l :=
  ⟨sourceLogKummer l u, ⟨u, rfl⟩⟩

theorem sourceLogKummer_frobenius (u : sourcePrincipalUnits l) :
    sourceLogKummer l (sourceFrobenius l u) =
      (l.value : sourceLocalField l) * sourceLogKummer l u := by
  change principalUnitLog (K := sourceLocalField l) (u ^ l.value) =
    (l.value : sourceLocalField l) * principalUnitLog (K := sourceLocalField l) u
  exact principalUnitLog_pow (K := sourceLocalField l) l.value l.value u

noncomputable def sourcePScaling (x : sourceLogShell l) : sourceLogShell l :=
  ⟨(l.value : sourceLocalField l) * (x : sourceLocalField l), by
    rcases x.property with ⟨u, hu⟩
    refine ⟨sourceFrobenius l u, ?_⟩
    rw [← hu]
    exact sourceLogKummer_frobenius l u⟩

theorem sourceLogKummer_square (u : sourcePrincipalUnits l) :
    sourceLogKummerShell l (sourceFrobenius l u) =
      sourcePScaling l (sourceLogKummerShell l u) := by
  apply Subtype.ext
  exact sourceLogKummer_frobenius l u

theorem concreteLogShellField_eq_adicCompletion :
    concreteLogShellField =
      concreteHeightOneSpectrum.adicCompletion GaussianField := rfl

theorem sourceTheater_localCarrier_q :
    (concreteInitialThetaCStage l).localCarrier.parameter.q =
      (l.value : ℚ_[l.value]) :=
  (concreteInitialThetaCStage l).localCarrier.q_is_prime

theorem sourcePScaling_nontrivial :
    ∃ x : sourceLogShell l, sourcePScaling l x ≠ x := by
  have h5 : (5 : ℝ) ≤ (l.value : ℝ) := by exact_mod_cast l.ge_five
  have hp1 : (1 : ℝ) < (l.value : ℝ) := by linarith
  have hp3 : (3 : ℝ) ≤ (l.value : ℝ) := by linarith
  have hnorm : ‖(l.value : ℚ_[l.value])‖ = (l.value : ℝ)⁻¹ :=
    Padic.norm_p
  have hthreshold : (1 : ℝ) / ((l.value : ℝ) - 1) < 1 := by
    have hpos : (0 : ℝ) < (l.value : ℝ) - 1 := by linarith
    rw [div_lt_one hpos]
    linarith
  have hsharp : (l.value : ℝ)⁻¹ < sharpInverseRadius l.value := by
    rw [show (l.value : ℝ)⁻¹ = (l.value : ℝ) ^ (-1 : ℝ) from
      (Real.rpow_neg_one _).symm]
    rw [sharpInverseRadius, sharpInverseValuationThreshold]
    apply Real.rpow_lt_rpow_of_exponent_lt hp1
    linarith
  have hr : (0 : ℝ) ≤ (l.value : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
  have hy : ‖(l.value : ℚ_[l.value])‖ ≤ (l.value : ℝ)⁻¹ := le_of_eq hnorm
  have hy_mem : (l.value : ℚ_[l.value]) ∈
      (principalUnitLogImage (K := ℚ_[l.value]) l.value :
        Set ℚ_[l.value]) :=
    principalUnitLogImage_contains_sharp_ball (K := ℚ_[l.value]) l.value
      hr hsharp hy
  refine ⟨⟨(l.value : ℚ_[l.value]), hy_mem⟩, ?_⟩
  intro h
  have hval : (l.value : ℚ_[l.value]) * (l.value : ℚ_[l.value]) =
      (l.value : ℚ_[l.value]) := congrArg Subtype.val h
  have hp0 : (l.value : ℚ_[l.value]) ≠ 0 := by
    exact_mod_cast (Nat.Prime.ne_zero l.prime)
  have hp1' : (l.value : ℚ_[l.value]) ≠ 1 := by
    intro h
    have h1 : l.value = 1 := by exact_mod_cast h
    have hge : 5 ≤ l.value := l.ge_five
    omega
  exact hp1' (mul_left_cancel₀ hp0 (by simpa using hval))

noncomputable def independentSourceFrobeniusLogKummerCard :
    SourceFrobeniusLogKummerCard l where
  sourcePrincipalUnits := sourcePrincipalUnits l
  sourceFrobenius := sourceFrobenius l
  sourceLogShell := sourceLogShell l
  logKummer := sourceLogKummerShell l
  pScaling := sourcePScaling l
  logKummer_frobenius := sourceLogKummer_square l
  pScaling_nontrivial := sourcePScaling_nontrivial l

end SourceOverQl

/-! ## 3. The exact source/target place-model mismatch and remaining card -/

theorem sourceComparison_obstruction (l : PrimeGeFive) :
    (concreteLogShellField =
        concreteHeightOneSpectrum.adicCompletion GaussianField) ∧
      ((concreteInitialThetaCStage l).localCarrier.parameter.q =
        (l.value : ℚ_[l.value])) ∧
      ((sourceLogShell l : Set ℚ_[l.value]) =
        (principalUnitLogImage (K := ℚ_[l.value]) l.value : Set ℚ_[l.value])) :=
  ⟨concreteLogShellField_eq_adicCompletion,
    sourceTheater_localCarrier_q l, rfl⟩

abbrev SourceLogKummerIdentificationCard (l : PrimeGeFive) :=
  SourceFrobeniusLogKummerIdentificationCard l LogKummerMap.logKummerData


/-! ## 4. The actual Q_5 field-level comparison with the concrete Gaussian completion -/

section QFiveFieldComparison

open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge

/-- The rational prime below the concrete Gaussian place is 5. -/
theorem concretePlace_rationalPrime_eq_five :
    (completionRationalPrime concretePlace).val = 5 := by
  unfold completionRationalPrime
  rw [show comap (k := ℚ) concretePlace = concreteFivePlace from by
    simpa [concretePlace] using concreteGaussianFivePlace_comap]
  rw [concreteFivePlace_maximalIdeal]
  rw [concreteFiveHeightOne]
  exact congrArg (fun p : Nat.Primes => p.val)
    (Equiv.apply_symm_apply
      (Rat.HeightOneSpectrum.primesEquiv (R := NumberField.RingOfIntegers ℚ))
      concreteFivePrime)

/-- The completion degree at the concrete Gaussian place over the lower
Q_5-completion is one (task-119 certificate). -/
theorem concretePlace_completion_finrank_eq_one :
    Module.finrank (Completion (comap (k := ℚ) concretePlace))
      (Completion concretePlace) = 1 :=
  concreteGaussianFivePlace_completion_finrank_eq_one

/-- The actual completion embedding is surjective because the completion degree
is one: an injective linear map from the one-dimensional lower completion into
the one-dimensional upper completion is bijective. -/
theorem concretePlace_completionMap_surjective :
    Function.Surjective (completionMap (k := ℚ) concretePlace) := by
  let L := Completion (comap (k := ℚ) concretePlace)
  let U := Completion concretePlace
  have hfin : Module.finrank L U = 1 := concretePlace_completion_finrank_eq_one
  have hdim : Module.finrank L L = Module.finrank L U := by
    rw [Module.finrank_self, hfin]
  have hinj : Function.Injective (algebraMap L U) := by
    change Function.Injective (completionMap (k := ℚ) concretePlace)
    exact completionMap_injective (k := ℚ) concretePlace
  have hlin : Function.Injective (Algebra.linearMap L U) := by
    intro x y h
    apply hinj
    simpa only [Algebra.linearMap_apply] using h
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hlin
  intro y
  obtain ⟨x, hx⟩ := hsurj y
  refine ⟨x, ?_⟩
  rw [Algebra.linearMap_apply] at hx
  exact hx

/-- The actual Q_5-comparison: the lower completion at the rational prime 5 and
the completion of the Gaussian field at the concrete place are equal as rings. -/
noncomputable def concretePlace_qFiveComparisonRingEquiv :
    Completion (comap (k := ℚ) concretePlace) ≃+* Completion concretePlace :=
  RingEquiv.ofBijective (completionMap (k := ℚ) concretePlace)
    ⟨completionMap_injective (k := ℚ) concretePlace,
      concretePlace_completionMap_surjective⟩

end QFiveFieldComparison

section QFiveTransport

open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits

theorem concretePlace_lower_absNorm :
    (Ideal.absNorm (comap (k := ℚ) concretePlace).maximalIdeal.asIdeal : ℝ) = 5 := by
  rw [show (comap (k := ℚ) concretePlace).maximalIdeal.asIdeal =
      concreteFiveHeightOne.asIdeal by
    rw [show comap (k := ℚ) concretePlace = concreteFivePlace from by
      simpa [concretePlace] using concreteGaussianFivePlace_comap]
    rw [concreteFivePlace_maximalIdeal]]
  rw [concreteFiveHeightOne_asIdeal_eq_span, gaussianRationalFive_absNorm]
  norm_num

theorem concretePlace_upper_absNorm :
    (Ideal.absNorm concretePlace.maximalIdeal.asIdeal : ℝ) = 5 := by
  rcases concreteGaussianFivePlace_maximalIdeal_eq_plus_or_minus with h | h
  · rw [show concretePlace.maximalIdeal.asIdeal = gaussianFieldFivePrimePlus from h,
      gaussianFieldFivePrimePlus_absNorm]
    norm_num
  · rw [show concretePlace.maximalIdeal.asIdeal = gaussianFieldFivePrimeMinus from h,
      gaussianFieldFivePrimeMinus_absNorm]
    norm_num

theorem concretePlace_norm_completionMap_eq
    (x : Completion (comap (k := ℚ) concretePlace)) :
    ‖completionMap (k := ℚ) concretePlace x‖ = ‖x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  · have hmap : completionMap (k := ℚ) concretePlace x ≠ 0 := fun h =>
      hx (completionMap_injective (k := ℚ) concretePlace (by simpa using h))
    rw [NumberFieldFinitePlace.norm_eq_absNorm_zpow concretePlace
        (completionMap (k := ℚ) concretePlace x) hmap,
      NumberFieldFinitePlace.norm_eq_absNorm_zpow (comap (k := ℚ) concretePlace) x hx,
      concretePlace_upper_absNorm, concretePlace_lower_absNorm]
    have hval := toAdd_valuation_completionMap (k := ℚ) concretePlace x hx hmap
    rw [concreteGaussianFivePlace_relativeRamificationIndex_eq_one] at hval
    simp only [Nat.cast_one, one_mul] at hval
    rw [hval]

theorem concretePlace_norm_qFiveComparisonRingEquiv
    (x : Completion (comap (k := ℚ) concretePlace)) :
    ‖concretePlace_qFiveComparisonRingEquiv x‖ = ‖x‖ := by
  change ‖completionMap (k := ℚ) concretePlace x‖ = ‖x‖
  exact concretePlace_norm_completionMap_eq x

theorem concretePlace_norm_qFiveComparisonRingEquiv_symm
    (y : Completion concretePlace) :
    ‖concretePlace_qFiveComparisonRingEquiv.symm y‖ = ‖y‖ := by
  have h := concretePlace_norm_qFiveComparisonRingEquiv
    (concretePlace_qFiveComparisonRingEquiv.symm y)
  rw [RingEquiv.apply_symm_apply] at h
  exact h.symm

noncomputable def concretePlace_integersRingEquiv :
    Integers (Completion (comap (k := ℚ) concretePlace)) ≃+*
      Integers (Completion concretePlace) :=
  concretePlace_qFiveComparisonRingEquiv.restrict _ _ fun x => by
    rw [LocalFieldIntegralUnits.mem_integers_iff,
      LocalFieldIntegralUnits.mem_integers_iff,
      concretePlace_norm_qFiveComparisonRingEquiv x]

noncomputable def concretePlace_unitsEquiv :
    (Integers (Completion (comap (k := ℚ) concretePlace)))ˣ ≃*
      (Integers (Completion concretePlace))ˣ :=
  Units.mapEquiv concretePlace_integersRingEquiv.toMulEquiv

theorem concretePlace_unitsEquiv_coe
    (u : (Integers (Completion (comap (k := ℚ) concretePlace)))ˣ) :
    ((concretePlace_unitsEquiv u : (Integers (Completion concretePlace))ˣ).val :
        Completion concretePlace) =
      concretePlace_qFiveComparisonRingEquiv
        (u.val : Completion (comap (k := ℚ) concretePlace)) := rfl

noncomputable def concretePlace_principalUnitsEquiv :
    principalUnits (K := Completion (comap (k := ℚ) concretePlace)) ≃
      principalUnits (K := Completion concretePlace) where
  toFun u := ⟨concretePlace_unitsEquiv u, by
    change ‖((concretePlace_unitsEquiv u :
      (Integers (Completion concretePlace))ˣ).val : Completion concretePlace) - 1‖ < 1
    rw [concretePlace_unitsEquiv_coe, ← map_one concretePlace_qFiveComparisonRingEquiv,
      ← map_sub, concretePlace_norm_qFiveComparisonRingEquiv]
    exact u.property⟩
  invFun v := ⟨concretePlace_unitsEquiv.symm v, by
    change ‖((concretePlace_unitsEquiv.symm v :
      (Integers (Completion (comap (k := ℚ) concretePlace)))ˣ).val :
      Completion (comap (k := ℚ) concretePlace)) - 1‖ < 1
    rw [show ((concretePlace_unitsEquiv.symm v :
          (Integers (Completion (comap (k := ℚ) concretePlace)))ˣ).val :
        Completion (comap (k := ℚ) concretePlace)) =
        concretePlace_qFiveComparisonRingEquiv.symm
          (v.val : Completion concretePlace) from rfl]
    rw [← map_one concretePlace_qFiveComparisonRingEquiv.symm, ← map_sub,
      concretePlace_norm_qFiveComparisonRingEquiv_symm]
    exact v.property⟩
  left_inv u := Subtype.ext (concretePlace_unitsEquiv.symm_apply_apply u)
  right_inv v := Subtype.ext (concretePlace_unitsEquiv.apply_symm_apply v)

end QFiveTransport

end LeanFormal.IUT.IUTII.Frobenioid.Example36
