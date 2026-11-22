import tmp.sheaf.xif.paper.S1512ProductHaarScalingActual
import LeanFormal.IUT.ABCBridge.Geometry.RationalCommonPrimeFinrank
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionNormTransport
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicHaarScaling
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import LeanFormal.IUT.ABCBridge.Geometry.AdicCompletionValuationUniqueness
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Normed.Module.FiniteDimension


/-!
# S1552: actual local and product Haar scaling at dependent finite places

The local additive Haar character of the inverse residue characteristic at a
rational finite place is transported across the actual continuous ring
equivalence between the canonical completion and Q_p.  The Q_p side is the
donor theorem of FinitePadicHaarScaling.  This proves the previously missing
local measure/character statement S1502LocalPrimeScaling without assuming a
normed Q_p structure on the canonical completion.

The product unit ball is compact (its norm unit ball is the completed valuation
ring), and Haar uniqueness on that compact set compares the canonical additive
Haar measure with the product of the local Haar measures.  The coordinatewise
diagonal unit acts as the product of the local inverse-prime dilations, giving
S1502ProductScalingMeasure.  A second application of second-countable Haar
uniqueness gives the global product decomposition
S1512ProductHaarDecomposition.  Finally, the existing consumer
s1502DependentProductScalingChar_of_measure yields
DependentProductScalingChar.

No unfinished proof and no added assumption is used in the scaling law;
only the concrete compact unit region is used.
-/

noncomputable section
open MeasureTheory
open scoped Pointwise ENNReal NNReal
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1422HDDDetActual
open LeanFormal.IUT.XiFPaper.S1502DependentScalingCharActual
open LeanFormal.IUT.XiFPaper.S1512ProductHaarScalingActual

namespace LeanFormal.IUT.XiFPaper.S1552ProductScalingMeasureActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

local instance completionMeasurableSpace (P : NumberField.FinitePlace ℚ) :
    MeasurableSpace (Completion P) := borel (Completion P)

local instance completionBorelSpace (P : NumberField.FinitePlace ℚ) :
    BorelSpace (Completion P) := ⟨rfl⟩

local instance instAlgebraRatCompletionAux (P : NumberField.FinitePlace ℚ) :
    Algebra ℚ (Completion P) :=
  @IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
    (NumberField.RingOfIntegers ℚ) _ _ ℚ ℚ _ _ _ _ P.maximalIdeal (Algebra.id ℚ)

local instance factTargetPrime (P : NumberField.FinitePlace ℚ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv P.maximalIdeal).val) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv P.maximalIdeal).property⟩

noncomputable def ringEquivCompletionPadic (P : NumberField.FinitePlace ℚ) :
    Completion P ≃+* ℚ_[(Rat.HeightOneSpectrum.primesEquiv P.maximalIdeal).val] :=
  (Rat.HeightOneSpectrum.adicCompletion.padicEquiv P.maximalIdeal :
    Completion P ≃+* ℚ_[(Rat.HeightOneSpectrum.primesEquiv P.maximalIdeal).val])

theorem distribHaarChar_completionPadic
    (P : NumberField.FinitePlace ℚ)
    (u : (Completion P)ˣ) :
    distribHaarChar (Completion P) u =
      distribHaarChar ℚ_[(Rat.HeightOneSpectrum.primesEquiv P.maximalIdeal).val]
        (Units.map (ringEquivCompletionPadic P).toMonoidHom u) := by
  let pP : ℕ := (Rat.HeightOneSpectrum.primesEquiv P.maximalIdeal).val
  letI : Fact (Nat.Prime pP) :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv P.maximalIdeal).property⟩
  letI : MeasurableSpace ℚ_[pP] := borel ℚ_[pP]
  letI : BorelSpace ℚ_[pP] := ⟨rfl⟩
  let e : Completion P ≃+* ℚ_[pP] := ringEquivCompletionPadic P
  have he : Continuous e :=
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv P.maximalIdeal).continuous
  have he' : Continuous e.symm :=
    (Rat.HeightOneSpectrum.adicCompletion.padicEquiv P.maximalIdeal).symm.continuous
  let eHomeo : Completion P ≃ₜ ℚ_[pP] :=
    { e.toEquiv with continuous_toFun := he, continuous_invFun := he' }
  let ν : Measure ℚ_[pP] := Measure.addHaar
  let μ : Measure (Completion P) := ν.map e.symm
  haveI hνreg : Measure.Regular ν := inferInstance
  haveI hμ : Measure.IsAddHaarMeasure μ :=
    AddEquiv.isAddHaarMeasure_map ν e.symm.toAddEquiv he' he
  haveI hreg : Measure.Regular μ := by
    change (Measure.map eHomeo.symm ν).Regular
    exact Measure.Regular.map eHomeo.symm
  let T : Set ℚ_[pP] := Metric.closedBall (0 : ℚ_[pP]) 1
  let S : Set (Completion P) := e.symm '' T
  have hTpos : 0 < ν T := by
    apply Measure.measure_pos_of_nonempty_interior ν
    refine ⟨0, ?_⟩
    refine mem_interior_iff_mem_nhds.mpr ?_
    exact Filter.mem_of_superset
      (Metric.isOpen_ball.mem_nhds (by simp : (0 : ℚ_[pP]) ∈ Metric.ball 0 1))
      (by simp [T, Metric.ball_subset_closedBall])
  have hTfin : ν T < ⊤ := by
    simp only [T]
    exact isCompact_closedBall (0 : ℚ_[pP]) 1 |>.measure_lt_top
  have hSmeas : MeasurableSet (u • S) := by
    have hScompact : IsCompact S := by
      simp only [S, T]
      exact isCompact_closedBall (0 : ℚ_[pP]) 1 |>.image he'
    have hcont : Continuous (fun x : Completion P => (u : Completion P) * x) :=
      continuous_const.mul continuous_id
    exact (hScompact.image hcont).isClosed.measurableSet
  have hmapT : (Measure.map e.symm ν) (e.symm '' T) = ν T := by
    have hSmeasT : MeasurableSet (e.symm '' T) := by
      have hc : IsCompact (e.symm '' T) := by
        simp only [T]
        exact isCompact_closedBall (0 : ℚ_[pP]) 1 |>.image he'
      exact hc.isClosed.measurableSet
    rw [show (Measure.map e.symm ν) (e.symm '' T) =
        ν (e.symm ⁻¹' (e.symm '' T)) from
      Measure.map_apply (μ := ν) (f := e.symm) he'.measurable hSmeasT]
    rw [Set.preimage_image_eq _ e.symm.injective]
  have hST : μ S = ν T := by
    simp only [S, μ]
    exact hmapT
  have hSpos : 0 < μ S := by rw [hST]; exact hTpos
  have hSfin : μ S < ⊤ := by rw [hST]; exact hTfin
  have hscale : μ (u • S) = (distribHaarChar ℚ_[pP] (Units.map e.toMonoidHom u)) * μ S := by
    have hmap : e '' (u • S) = (Units.map e.toMonoidHom u : (ℚ_[pP])ˣ) • T := by
      ext y
      constructor
      · rw [Set.mem_smul_set]
        rintro ⟨x, hx, hxy⟩
        subst hxy
        rw [Set.mem_smul_set] at hx
        rcases hx with ⟨s, hs, hsmul⟩
        subst hsmul
        simp only [S, T] at hs
        rcases hs with ⟨t, ht, rfl⟩
        refine ⟨t, ht, ?_⟩
        calc
          (Units.map e.toMonoidHom u : (ℚ_[pP])ˣ) • t = (e u : ℚ_[pP]) * t := by
            change ((Units.map e.toMonoidHom u : (ℚ_[pP])ˣ) : ℚ_[pP]) * t = (e u : ℚ_[pP]) * t
            rfl
          _ = e u * e (e.symm t) := by rw [e.apply_symm_apply]
          _ = e (u * e.symm t) := by rw [map_mul]
          _ = e (u • e.symm t) := rfl
      · rw [Set.mem_smul_set]
        rintro ⟨t, ht, hty⟩
        subst hty
        rw [Set.mem_image]
        refine ⟨(u : Completion P) * e.symm t, ?_, ?_⟩
        · rw [Set.mem_smul_set]
          exact ⟨e.symm t, by simp only [S, T]; exact ⟨t, ht, rfl⟩, rfl⟩
        · calc
            e ((u : Completion P) * e.symm t) = e u * e (e.symm t) := by rw [map_mul]
            _ = e u * t := by rw [e.apply_symm_apply]
            _ = (Units.map e.toMonoidHom u : (ℚ_[pP])ˣ) • t := by
              change (e u : ℚ_[pP]) * t = ((Units.map e.toMonoidHom u : (ℚ_[pP])ˣ) : ℚ_[pP]) * t
              rfl
    have hpre : e.symm ⁻¹' (u • S) = e '' (u • S) :=
      (e.image_eq_preimage_symm (u • S)).symm
    have hcalc : μ (u • S) = ν ((Units.map e.toMonoidHom u : (ℚ_[pP])ˣ) • T) := by
      calc
        μ (u • S) = ν (e.symm ⁻¹' (u • S)) := by
          change (Measure.map e.symm ν) (u • S) = _
          exact Measure.map_apply (μ := ν) (f := e.symm) he'.measurable hSmeas
        _ = ν (e '' (u • S)) := by rw [hpre]
        _ = ν ((Units.map e.toMonoidHom u : (ℚ_[pP])ˣ) • T) := by rw [hmap]
    rw [hcalc, hST]
    exact (distribHaarChar_mul ν (Units.map e.toMonoidHom u) T).symm
  exact distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) hSpos.ne' hSfin.ne hscale


theorem distribHaarChar_padicPrimeInv (p : ℕ) [Fact p.Prime] :
    distribHaarChar ℚ_[p]
      (Units.mk0 ((p : ℚ_[p])⁻¹)
        (inv_ne_zero (Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero))) =
      (p : ℝ≥0) := by
  letI : MeasurableSpace ℚ_[p] := borel ℚ_[p]
  letI : BorelSpace ℚ_[p] := ⟨rfl⟩
  let u : ℚ_[p]ˣ := Units.mk0 (p : ℚ_[p])
    (Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero)
  have hchar : distribHaarChar ℚ_[p] u = (p : ℝ≥0)⁻¹ := by
    let μ : Measure ℚ_[p] := Measure.addHaar
    let T : Set ℚ_[p] := Metric.closedBall (0 : ℚ_[p]) 1
    have hTpos : 0 < μ T := by
      apply Measure.measure_pos_of_nonempty_interior μ
      refine ⟨0, ?_⟩
      refine mem_interior_iff_mem_nhds.mpr ?_
      exact Filter.mem_of_superset
        (Metric.isOpen_ball.mem_nhds (by simp : (0 : ℚ_[p]) ∈ Metric.ball 0 1))
        (by simp [T, Metric.ball_subset_closedBall])
    have hTfin : μ T < ⊤ := by
      simp only [T]
      exact isCompact_closedBall (0 : ℚ_[p]) 1 |>.measure_lt_top
    refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) hTpos.ne' hTfin.ne ?_
    have h := LeanFormal.IUT.FinitePadicHaarScaling.measure_prime_smul_finiteDimensional
      (p := p) (M := ℚ_[p]) μ T
    have hfin : Module.finrank ℚ_[p] ℚ_[p] = 1 := Module.finrank_self ℚ_[p]
    rw [hfin] at h
    simpa [u, Units.smul_def, ENNReal.coe_inv, ENNReal.coe_natCast,
      ENNReal.coe_pow] using h
  have hu : u⁻¹ = Units.mk0 ((p : ℚ_[p])⁻¹)
      (inv_ne_zero (Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero)) := by
    ext
    simp [u]
  rw [← hu]
  rw [show (distribHaarChar ℚ_[p]) u⁻¹ = ((distribHaarChar ℚ_[p]) u)⁻¹ from map_inv _ _]
  rw [hchar, inv_inv]

theorem hcomap (P : NumberField.FinitePlace ℚ) : comap (k := ℚ) P = P := by
  apply NumberField.FinitePlace.maximalIdeal_injective
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rw [NumberFieldFinitePlace.comap_maximalIdeal]
  change Ideal.comap (RingHom.id (NumberField.RingOfIntegers ℚ)) P.maximalIdeal.asIdeal =
    P.maximalIdeal.asIdeal
  rw [Ideal.comap_id]

theorem completionRationalPrime_eq (P : NumberField.FinitePlace ℚ) :
    completionRationalPrime P = Rat.HeightOneSpectrum.primesEquiv P.maximalIdeal := by
  unfold completionRationalPrime
  apply congrArg Rat.HeightOneSpectrum.primesEquiv
  exact congrArg NumberField.FinitePlace.maximalIdeal (hcomap P)

theorem dependentPlacePrime_eq (s : Finset (NumberField.FinitePlace ℚ))
    (v : {v // v ∈ s}) :
    dependentPlacePrime s v =
      (Rat.HeightOneSpectrum.primesEquiv v.1.maximalIdeal).val := by
  unfold dependentPlacePrime
  rw [completionRationalPrime_eq]

theorem unit_map_dependentPrimeInverseUnit
    (s : Finset (NumberField.FinitePlace ℚ)) (v : {v // v ∈ s}) :
    Units.map (ringEquivCompletionPadic v.1).toMonoidHom
        (dependentPrimeInverseUnit s v) =
      Units.mk0
        (((Rat.HeightOneSpectrum.primesEquiv v.1.maximalIdeal).val : ℚ_[
            (Rat.HeightOneSpectrum.primesEquiv v.1.maximalIdeal).val])⁻¹)
        (inv_ne_zero (Nat.cast_ne_zero.mpr
          (Rat.HeightOneSpectrum.primesEquiv v.1.maximalIdeal).property.ne_zero)) := by
  ext
  simp only [Units.coe_map, Units.val_mk0, dependentPrimeInverseUnit]
  change (ringEquivCompletionPadic v.1) ((dependentPlacePrime s v : Completion v.1)⁻¹) =
    ((Rat.HeightOneSpectrum.primesEquiv v.1.maximalIdeal).val : ℚ_[
      (Rat.HeightOneSpectrum.primesEquiv v.1.maximalIdeal).val])⁻¹
  rw [map_inv₀]
  congr 1
  rw [dependentPlacePrime_eq]
  exact map_natCast (ringEquivCompletionPadic v.1)
    (Rat.HeightOneSpectrum.primesEquiv v.1.maximalIdeal).val

theorem localScaling (s : Finset (NumberField.FinitePlace ℚ))
    (v : {v // v ∈ s}) : S1502LocalPrimeScaling s v := by
  unfold S1502LocalPrimeScaling
  let P := v.1
  let pP : ℕ := (Rat.HeightOneSpectrum.primesEquiv P.maximalIdeal).val
  letI : Fact (Nat.Prime pP) :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv P.maximalIdeal).property⟩
  have hchar := distribHaarChar_completionPadic P
    (dependentPrimeInverseUnit s v)
  have hpad := distribHaarChar_padicPrimeInv pP
  have hunit := unit_map_dependentPrimeInverseUnit s v
  have hval : pP = dependentPlacePrime s v := (dependentPlacePrime_eq s v).symm
  have hmain : distribHaarChar (Completion P) (dependentPrimeInverseUnit s v) =
      (dependentPlacePrime s v : ℝ≥0) := by
    rw [hchar, hunit, hpad, hval]
  exact_mod_cast hmain




/-! ## 6. The norm unit ball is the compact valuation ring -/

theorem norm_le_one_iff_valued_le_one {F : Type*} [Field F] [NumberField F]
    (P : NumberField.FinitePlace F) (x : Completion P) :
    ‖x‖ ≤ 1 ↔ (Valued.v x : WithZero (Multiplicative ℤ)) ≤ 1 := by
  by_cases hx : x = 0
  · subst x
    simp
  · let ν : ℤ := Multiplicative.toAdd
      (WithZero.unzero (valuation_ne_zero_of_ne_zero P x hx))
    have hv : (Valued.v x : WithZero (Multiplicative ℤ)) = WithZero.exp ν := by
      dsimp [ν]
      exact (WithZero.coe_unzero (valuation_ne_zero_of_ne_zero P x hx)).symm
    have hbase : (1 : ℝ) < (Ideal.absNorm P.maximalIdeal.asIdeal : ℝ) := by
      exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm P.maximalIdeal
    have hnorm : ‖x‖ = (Ideal.absNorm P.maximalIdeal.asIdeal : ℝ) ^ ν := by
      dsimp [ν]
      exact norm_eq_absNorm_zpow P x hx
    rw [hnorm, zpow_le_one_iff_right₀ hbase]
    rw [hv, show (1 : WithZero (Multiplicative ℤ)) = WithZero.exp (0 : ℤ) from
      WithZero.exp_zero.symm]
    rw [WithZero.exp_le_exp]

theorem isCompact_norm_unitBall (P : NumberField.FinitePlace ℚ) :
    IsCompact {x : Completion P | ‖x‖ ≤ 1} := by
  have hset : {x : Completion P | ‖x‖ ≤ 1} =
      (CompletionIntegers P : Set (Completion P)) := by
    ext x
    change ‖x‖ ≤ 1 ↔ x ∈
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ P.maximalIdeal :
        Set (Completion P))
    exact (norm_le_one_iff_valued_le_one P x).trans
      (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
        (R := NumberField.RingOfIntegers ℚ) (K := ℚ) (v := P.maximalIdeal)).symm
  rw [hset]
  have h : CompactSpace
      ((comap (k := ℚ) P).maximalIdeal.adicCompletionIntegers ℚ) :=
    compactSpace_adicCompletionIntegers (k := ℚ) (K := ℚ) P
  rw [hcomap P] at h
  exact isCompact_iff_compactSpace.mpr h

theorem isCompact_dependentUnitRegion
    (s : Finset (NumberField.FinitePlace ℚ)) :
    IsCompact (dependentUnitRegion s) := by
  have hset : dependentUnitRegion s =
      Set.pi Set.univ (fun v : {v // v ∈ s} => {x : Completion v.1 | ‖x‖ ≤ 1}) := by
    ext x
    simp [dependentUnitRegion, LocalFieldProductHull.unitRegion, Set.mem_pi]
  rw [hset]
  exact isCompact_univ_pi (fun v => isCompact_norm_unitBall v.1)


/-! ## 7. Coordinatewise action and product measure -/

theorem coe_dependentPrimeUnit
    (s : Finset (NumberField.FinitePlace ℚ)) :
    (dependentPrimeUnit s : dependentPoint s) =
      fun v => (dependentPrimeInverseUnit s v : Completion v.1) := by
  ext v
  simp [dependentPrimeUnit]

theorem dependentPrimeUnit_smul_unitRegion_eq
    (s : Finset (NumberField.FinitePlace ℚ)) :
    dependentPrimeUnit s • dependentUnitRegion s =
      Set.pi Set.univ (fun v : {v // v ∈ s} =>
        dependentPrimeInverseUnit s v • {x : Completion v.1 | ‖x‖ ≤ 1}) := by
  have hU : dependentUnitRegion s =
      Set.pi Set.univ (fun v : {v // v ∈ s} => {x : Completion v.1 | ‖x‖ ≤ 1}) := by
    ext x
    simp [dependentUnitRegion, LocalFieldProductHull.unitRegion, Set.mem_pi]
  rw [hU]
  change (fun x : dependentPoint s => (dependentPrimeUnit s : dependentPoint s) * x) ''
      Set.pi Set.univ (fun v : {v // v ∈ s} => {x : Completion v.1 | ‖x‖ ≤ 1}) =
    Set.pi Set.univ (fun v : {v // v ∈ s} =>
      dependentPrimeInverseUnit s v • {x : Completion v.1 | ‖x‖ ≤ 1})
  rw [show (fun x : dependentPoint s => (dependentPrimeUnit s : dependentPoint s) * x) =
      Pi.map (fun v : {v // v ∈ s} =>
        fun y : Completion v.1 => (dependentPrimeInverseUnit s v : Completion v.1) * y) from by
    funext x v
    rw [coe_dependentPrimeUnit]
    rfl]
  rw [Set.piMap_image_univ_pi]
  apply Set.pi_congr rfl
  intro v _
  ext x
  rw [Set.mem_image, Set.mem_smul_set]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩

theorem localMeasureScaling
    (s : Finset (NumberField.FinitePlace ℚ)) (v : {v // v ∈ s})
    (S : Set (Completion v.1)) :
    (Measure.addHaar : Measure (Completion v.1))
        (dependentPrimeInverseUnit s v • S) =
      (dependentPlacePrime s v : ENNReal) *
        (Measure.addHaar : Measure (Completion v.1)) S := by
  have hchar := localScaling s v
  have h := distribHaarChar_mul
    (μ := (Measure.addHaar : Measure (Completion v.1)))
    (g := dependentPrimeInverseUnit s v) S
  rw [hchar] at h
  exact h.symm

theorem pi_unitRegion
    (s : Finset (NumberField.FinitePlace ℚ)) :
    Measure.pi (fun v : {v // v ∈ s} =>
        (Measure.addHaar : Measure (Completion v.1))) (dependentUnitRegion s) =
      ∏ v : {v // v ∈ s},
        (Measure.addHaar : Measure (Completion v.1))
          {x : Completion v.1 | ‖x‖ ≤ 1} := by
  have hU : dependentUnitRegion s =
      Set.pi Set.univ (fun v : {v // v ∈ s} => {x : Completion v.1 | ‖x‖ ≤ 1}) := by
    ext x
    simp [dependentUnitRegion, LocalFieldProductHull.unitRegion, Set.mem_pi]
  rw [hU, Measure.pi_pi]

theorem pi_scaled_unitRegion
    (s : Finset (NumberField.FinitePlace ℚ)) :
    Measure.pi (fun v : {v // v ∈ s} =>
        (Measure.addHaar : Measure (Completion v.1)))
        (dependentPrimeUnit s • dependentUnitRegion s) =
      ∏ v : {v // v ∈ s},
        (Measure.addHaar : Measure (Completion v.1))
          (dependentPrimeInverseUnit s v • {x : Completion v.1 | ‖x‖ ≤ 1}) := by
  rw [dependentPrimeUnit_smul_unitRegion_eq, Measure.pi_pi]


/-! ## 8. Product unit-ball scaling -/

theorem productScalingMeasure
    (s : Finset (NumberField.FinitePlace ℚ)) :
    S1502ProductScalingMeasure s := by
  unfold S1502ProductScalingMeasure
  let ν : Measure (dependentPoint s) :=
    Measure.pi (fun v : {v // v ∈ s} => (Measure.addHaar : Measure (Completion v.1)))
  let μ : Measure (dependentPoint s) := dependentHaar s
  haveI hν : Measure.IsAddHaarMeasure ν := inferInstance
  have hμν : ∀ K : Set (dependentPoint s), IsCompact K →
      μ K = (Measure.addHaarScalarFactor μ ν : ENNReal) * ν K := by
    intro K hK
    have h := Measure.measure_isAddInvariant_eq_smul_of_isCompact_closure
      (μ' := μ) (μ := ν) (s := K) (by rwa [hK.isClosed.closure_eq])
    simpa [Measure.nnreal_smul_coe_apply] using h
  have hUcompact : IsCompact (dependentUnitRegion s) :=
    isCompact_dependentUnitRegion s
  have hSUcompact : IsCompact (dependentPrimeUnit s • dependentUnitRegion s) := by
    have hcont : Continuous
        (fun x : dependentPoint s => (dependentPrimeUnit s : dependentPoint s) * x) :=
      continuous_const.mul continuous_id
    exact hUcompact.image hcont
  have hU := hμν (dependentUnitRegion s) hUcompact
  have hSU := hμν (dependentPrimeUnit s • dependentUnitRegion s) hSUcompact
  have hν_scaled : ν (dependentPrimeUnit s • dependentUnitRegion s) =
      (dependentExponent s : ENNReal) * ν (dependentUnitRegion s) := by
    rw [pi_scaled_unitRegion, pi_unitRegion]
    calc
      (∏ v : {v // v ∈ s}, (Measure.addHaar : Measure (Completion v.1))
          (dependentPrimeInverseUnit s v • {x : Completion v.1 | ‖x‖ ≤ 1}))
          = ∏ v : {v // v ∈ s}, (dependentPlacePrime s v : ENNReal) *
              (Measure.addHaar : Measure (Completion v.1))
                {x : Completion v.1 | ‖x‖ ≤ 1} := by
            apply Finset.prod_congr rfl
            intro v _
            exact localMeasureScaling s v {x : Completion v.1 | ‖x‖ ≤ 1}
      _ = (∏ v : {v // v ∈ s}, (dependentPlacePrime s v : ENNReal)) *
            ∏ v : {v // v ∈ s}, (Measure.addHaar : Measure (Completion v.1))
              {x : Completion v.1 | ‖x‖ ≤ 1} := by
            rw [Finset.prod_mul_distrib]
      _ = (dependentExponent s : ENNReal) *
            ∏ v : {v // v ∈ s}, (Measure.addHaar : Measure (Completion v.1))
              {x : Completion v.1 | ‖x‖ ≤ 1} := by
            congr 1
            rw [dependentExponent, Nat.cast_prod]
  calc
    μ (dependentPrimeUnit s • dependentUnitRegion s)
        = (Measure.addHaarScalarFactor μ ν : ENNReal) *
            ν (dependentPrimeUnit s • dependentUnitRegion s) := hSU
    _ = (Measure.addHaarScalarFactor μ ν : ENNReal) *
          ((dependentExponent s : ENNReal) * ν (dependentUnitRegion s)) := by
            rw [hν_scaled]
    _ = (dependentExponent s : ENNReal) *
          ((Measure.addHaarScalarFactor μ ν : ENNReal) * ν (dependentUnitRegion s)) := by
            rw [mul_left_comm]
    _ = (dependentExponent s : ENNReal) * μ (dependentUnitRegion s) := by
            rw [← hU]


/-! ## 9. Positivity and finiteness of the unit region -/

theorem dependentUnitRegion_pos
    (s : Finset (NumberField.FinitePlace ℚ)) :
    0 < dependentHaar s (dependentUnitRegion s) := by
  have hregion : LocalFieldProductHull.region
      (K := fun v : {v // v ∈ s} => Completion v.1) (fun _ => 1) =
        dependentUnitRegion s := by
    ext x
    simp [LocalFieldProductHull.region, dependentUnitRegion,
      LocalFieldProductHull.unitRegion]
  have hne : (interior (dependentUnitRegion s)).Nonempty := by
    rw [← hregion]
    exact ⟨0, LocalFieldProductHull.zero_mem_interior_region
      (K := fun v : {v // v ∈ s} => Completion v.1)
      (fun _ => 1) (fun _ => one_ne_zero)⟩
  exact Measure.measure_pos_of_nonempty_interior (dependentHaar s) hne

theorem dependentUnitRegion_lt_top
    (s : Finset (NumberField.FinitePlace ℚ)) :
    dependentHaar s (dependentUnitRegion s) < ⊤ :=
  (isCompact_dependentUnitRegion s).measure_lt_top

/-! ## 10. The global product measure decomposition -/

theorem productHaarDecomposition
    (s : Finset (NumberField.FinitePlace ℚ)) :
    S1512ProductHaarDecomposition s := by
  let ν : Measure (dependentPoint s) :=
    Measure.pi (fun v : {v // v ∈ s} => (Measure.addHaar : Measure (Completion v.1)))
  let μ : Measure (dependentPoint s) := dependentHaar s
  haveI hν : Measure.IsAddHaarMeasure ν := inferInstance
  haveI hsec : SecondCountableTopology (dependentPoint s) := inferInstance
  have h := Measure.isAddLeftInvariant_eq_smul (μ' := μ) (μ := ν)
  refine ⟨(Measure.addHaarScalarFactor μ ν : ENNReal), ?_, ENNReal.coe_ne_top, ?_⟩
  · exact ENNReal.coe_ne_zero.mpr
      (ne_of_gt (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ ν))
  · simpa [μ, ν, Measure.nnreal_smul_coe_apply] using h

/-! ## 11. The dependent character -/

theorem dependentProductScalingChar
    (s : Finset (NumberField.FinitePlace ℚ)) :
    DependentProductScalingChar s :=
  s1502DependentProductScalingChar_of_measure s (productScalingMeasure s)
    (dependentUnitRegion_pos s) (dependentUnitRegion_lt_top s)


theorem localCompletionScaling
    (s : Finset (NumberField.FinitePlace ℚ)) (v : {v // v ∈ s}) :
    S1512LocalCompletionScaling s v :=
  localScaling s v

theorem firstMissingMeasureLemma
    (s : Finset (NumberField.FinitePlace ℚ)) (v : {v // v ∈ s}) :
    S1512FirstMissingMeasureLemma s v :=
  localScaling s v

#print axioms localScaling
#print axioms productScalingMeasure
#print axioms productHaarDecomposition
#print axioms dependentProductScalingChar

end LeanFormal.IUT.XiFPaper.S1552ProductScalingMeasureActual
