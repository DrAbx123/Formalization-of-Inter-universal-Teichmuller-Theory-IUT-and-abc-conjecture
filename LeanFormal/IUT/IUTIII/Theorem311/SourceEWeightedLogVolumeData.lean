import LeanFormal.IUT.Audit.Status
import Mathlib

/-!
# E-weighted log-volumes: the normalization skeleton of IUT III, Remark 3.1.1, (ii)-(iv)

Paper anchors (pagewise plain text of "Inter-universal Teichmuller Theory III";
the layout transcription uses a different line numbering):

* (ii), :5509-5567: the normalized weight
  `1/[Kv:(Fmod)v] * sum_{w over vQ} [(Fmod)w : QvQ]` on the direct sum
  `log(alphaFvQ) = oplus_{v over vQ} log(alphaFv)`, normalized so that
  multiplication by pvQ changes log-volumes by addition or subtraction of
  log(pvQ) (sign according to vQ arithmetic or non-arithmetic archimedean);
  the tensor form uses `1/prod_alpha [Kv_alpha:(Fmod)v_alpha]` with a sum
  over collections of not necessarily distinct labels.
* (iii), :5568-5603: weighted sums of log-volumes do not in general arise as
  a positive multiple of the logarithm of a measure; direct product region
  (direct product of compact subsets of positive measure) and direct product
  pre-region (relatively compact) are introduced; for such regions the
  computation is stated to be completely straightforward.
* (iv), :5634-5746: the E-weighted measure muE from data (V, E, M): the
  compatible families M_{E*V} with bijection onto M_W, the measure structure
  transported from M_W, and for direct product regions the display
  `(1/N_E) * mu^log_E(S) = sum_v (1/N_v) * mu^log_v(S_v)` with
  `N_E = prod_v N_v` (:5739-5746; the "suitable normalization factor" of
  :5636).  muE is completely determined by the cardinalities N of E
  (:5657-5663).

## Our route (reduction) and deviations

* `EWeightedLogVolumeData` carries only the data (V, M, mu, N): by
  :5657-5663 the cardinalities of the finite sets E_v are all that enter, so
  the structure records `cardinality : V -> Nat` instead of the finite types
  E_v; the graph of (iv) is realized on the cardinality model
  `FiberIndex = Sigma v, Fin (N_{not v})` with the product measure on the
  fiber space.
* The normalization constant is *defined* as `kappa = 1/N_E` (the display
  pins it) rather than kept as a free structure field; identifying a
  source-side constant with it belongs to the supply card below.
* `eWeightedVolume` is the value of muE on a direct product region presented
  by its factorization data; the (iv) construction for general Borel sets
  (compatibility bookkeeping inside M_{E*V}) is not formalized here -- an
  explicit reduction point.  In particular no measure on M_V is created:
  the weighted sums are not additive in general (cf. the warning of (iii),
  :5573-5579).
* `kappa_log_eWeightedVolume_eq_weightedSum` (Q1) is the display of (iv) for
  measurable factor regions of positive finite measure.  The source states it
  for compact subsets of positive measure; compactness there only serves to
  make the volumes finite positive reals, which we assume directly, so no
  topology is introduced.
* `shift_pvQ_add_log` (Q2) is the abstract form of the normalization
  statement of (ii) (:5559-5567).  The per-place scaling law is the avatar of
  [AbsTopIII], Proposition 5.7, (i), (b) at the places under consideration.
  The arithmetic exponents e_v and the degree identity are not proved here;
  they are frozen as the named card
  `IUT-III.source-pvQ-shift-exponent-normalization`.
* Not claimed: the tensor product version with repeated labels is not
  formalized separately (it instantiates the same skeleton); the identity
  `(Ob3-3) det tensor M` is not touched.

## Cards and consumers

* Cards (status interface, no supplier claimed; see the Audit namespace):
  `IUT-III.source-E-weighted-measure-realization`,
  `IUT-III.source-pvQ-shift-exponent-normalization`,
  `IUT-III.source-E-weighted-log-volume-data` (file-level card).
* Consumers (read-only references this file is written against):
  - `Theorem311/SourceK1K2CardReduction.lean:194`
    (`ConcreteFiniteTheorem311.normalizedLogVolume_ind3Lift_add`), reused at
    `Theorem311/SourceK1K2VolumeTranslationLaw.lean:284`,
    `Theorem311/HullEnvelopeConditionsDischarge.lean:240/:257/:348` and
    `Theorem311/SourceK1K2Ind3ScalingAudit.lean:133/:149`: the concrete
    finite avatar of the normalized shift law; this file supplies the
    general interface whose source instantiation is the card above.
  - `Corollary312/StepXI/CertificateHullWiring.lean:247`
    (`sourceRealHullVolume`) and `:280` (`sourceRealHullVolume_ge_normalized`,
    Faraday line): the via-images normalization consumer.
  - Card-HULLREAL hull-volume normalization slot (see
    `wild-brainstorm-20261017.md`, section 23.E, E2, and section 25, S4).
-/

noncomputable section

namespace LeanFormal.IUT

namespace EWeightedLogVolume

open MeasureTheory
open scoped ENNReal

universe u v

set_option linter.checkUnivs false in
/-- Abstract data (V, E, M) of IUT III, Remark 3.1.1, (iv): a finite
nonempty index set, one measure space `(M v, mu v)` per index, and the
cardinalities `N v` of the finite sets `E v` (only the cardinalities matter,
cf. :5657-5663). -/
structure EWeightedLogVolumeData where
  V : Type u
  [fintypeV : Fintype V]
  [nonemptyV : Nonempty V]
  M : V → Type v
  [measureSpaceM : ∀ v, MeasureSpace (M v)]
  cardinality : V → ℕ
  cardinality_pos : ∀ v, 0 < cardinality v

attribute [instance] EWeightedLogVolumeData.fintypeV EWeightedLogVolumeData.nonemptyV EWeightedLogVolumeData.measureSpaceM

/-- The measurable space of `M v`, derived from the measure-space data (the
structure no longer carries it separately, so that `volume` and every
`Measure (M v)`-annotation see the same measurable space). -/
instance instMeasurableSpaceOfData (D : EWeightedLogVolumeData) (v : D.V) :
    MeasurableSpace (D.M v) :=
  (D.measureSpaceM v).toMeasurableSpace

namespace EWeightedLogVolumeData

variable (D : EWeightedLogVolumeData)

/-- `N_{not v} = prod_{v' != v} N v'`: the cardinality of `E_{not v}` of
(iv). -/
def fiberCardinality (v : D.V) : ℕ := by
  classical
  exact ∏ v' ∈ Finset.univ.erase v, D.cardinality v'

/-- `N_E = prod_v N v` of (iv). -/
def totalCardinality : ℕ := ∏ v, D.cardinality v

/-- The normalization constant `kappa = 1/N_E`: the "suitable normalization
factor" of :5636 and the display at :5739-5746. -/
def kappa : ℝ := (D.totalCardinality : ℝ)⁻¹

theorem fiberCardinality_pos (v : D.V) : 0 < D.fiberCardinality v := by
  classical
  rw [fiberCardinality]
  exact Finset.prod_pos fun v' _ => D.cardinality_pos v'

theorem totalCardinality_pos : 0 < D.totalCardinality :=
  Finset.prod_pos fun v _ => D.cardinality_pos v

theorem kappa_pos : 0 < D.kappa := by
  rw [kappa]
  exact inv_pos.mpr (by exact_mod_cast D.totalCardinality_pos)

/-- The fiber index set `coprod_v E_{not v} x {v}` (the set W of (iv)),
realized as a dependent sum with `Fin` fibers (only cardinalities are used,
cf. :5657-5663). -/
abbrev FiberIndex := Σ v : D.V, Fin (D.fiberCardinality v)

/-- The product of the `E_{not v}`-copies of the local spaces: the space `M_W`
of (iv) in the cardinality model. -/
abbrev FiberProduct := (i : D.FiberIndex) → D.M i.1

/-- The box `prod_v S_v^{E_{not v}}` inside the fiber product: for a direct
product region `S = prod_v S_v` this is the image of `S_E` under the
bijection `M_{E*V} -> M_W` of (iv) (see the file header for the
identification). -/
def regionFiberBox (S : ∀ v, Set (D.M v)) : Set D.FiberProduct :=
  Set.pi Set.univ fun i => S i.1

/-- The E-weighted volume of the direct product region `prod_v S_v` of
(ii)-(iv): the measure of `regionFiberBox S` with respect to the product
measure on `M_W`.  This is the quantity `muE(S)` of (iv) on direct product
regions. -/
def eWeightedVolume (S : ∀ v, Set (D.M v)) : ℝ≥0∞ :=
  (Measure.pi fun i : D.FiberIndex => (volume : Measure (D.M i.1)))
    (D.regionFiberBox S)

/-- The "straightforward computation" of (iv) (:5739-5746) at the
unnormalized level: the E-weighted volume of a direct product region is the
product of the factor volumes with the complementary cardinalities as
exponents, `muE(prod S_v) = prod_v mu_v(S_v)^{N_{not v}}`. -/
theorem eWeightedVolume_apply (hσ : ∀ v, SigmaFinite (volume : Measure (D.M v)))
    (S : ∀ v, Set (D.M v)) :
    D.eWeightedVolume S = ∏ v, (volume (S v)) ^ (D.fiberCardinality v) := by
  classical
  haveI : ∀ i : D.FiberIndex, SigmaFinite (volume : Measure (D.M i.1)) :=
    fun i => hσ i.1
  rw [eWeightedVolume, regionFiberBox, Measure.pi_pi]
  rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro v _
  dsimp only
  exact Fin.prod_const (D.fiberCardinality v) (volume (S v))

/-- The normalized weighted log-volume sum of (ii) (:5509-5567), displayed at
:5746 as the right-hand side: `sum_v (1/N_v) * mu^log_v(S_v)`. -/
def normalizedWeightedLogVolume (S : ∀ v, Set (D.M v)) : ℝ :=
  ∑ v, (D.cardinality v : ℝ)⁻¹ * Real.log ((volume (S v)).toReal)

/-- A direct product region in the sense of (iii) (:5588-5593), in the
measurable positive finite form used for the real-valued logarithm
(compactness as in the source is replaced by the finite positive measure
assumption it serves). -/
def IsDirectProductRegion (S : ∀ v, Set (D.M v)) : Prop :=
  ∀ v, MeasurableSet (S v) ∧ volume (S v) ≠ 0 ∧ volume (S v) ≠ ⊤

/-- **Q1** (Remark 3.1.1, (iv), display at :5739-5746, with the normalization
factor of :5636): the normalized logarithm of the E-weighted volume of a
direct product region equals the normalized weighted sum of the factor
log-volumes, `(1/N_E) * mu^log_E(S) = sum_v (1/N_v) * mu^log_v(S_v)`. -/
theorem kappa_log_eWeightedVolume_eq_weightedSum
    (hσ : ∀ v, SigmaFinite (volume : Measure (D.M v)))
    (S : ∀ v, Set (D.M v)) (hS : D.IsDirectProductRegion S) :
    D.kappa * Real.log ((D.eWeightedVolume S).toReal)
      = D.normalizedWeightedLogVolume S := by
  classical
  have hbox := D.eWeightedVolume_apply hσ S
  have htoReal : (D.eWeightedVolume S).toReal
      = ∏ v, ((volume (S v)).toReal) ^ (D.fiberCardinality v) := by
    rw [hbox]
    simp [ENNReal.toReal_pow]
  have hp : ∀ v, (volume (S v)).toReal ≠ 0 := fun v =>
    ne_of_gt (ENNReal.toReal_pos (hS v).2.1 (hS v).2.2)
  have hlog : Real.log ((D.eWeightedVolume S).toReal)
      = ∑ v, (D.fiberCardinality v : ℝ) * Real.log ((volume (S v)).toReal) := by
    rw [htoReal]
    rw [Real.log_prod (fun v _ => pow_ne_zero _ (hp v))]
    apply Finset.sum_congr rfl
    intro v _
    exact Real.log_pow _ _
  rw [hlog, normalizedWeightedLogVolume, kappa, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [← mul_assoc]
  congr 1
  have hcast : ((D.fiberCardinality v : ℕ) : ℝ) * (D.cardinality v : ℝ)
      = (D.totalCardinality : ℝ) := by
    rw [fiberCardinality, totalCardinality]
    have h := Finset.prod_erase_mul (Finset.univ : Finset D.V) D.cardinality
      (Finset.mem_univ v)
    exact_mod_cast h
  have hN : (D.cardinality v : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (D.cardinality_pos v))
  have hTN : (D.totalCardinality : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt D.totalCardinality_pos)
  field_simp
  linarith [hcast]

/-- Per-place scaling datum for the pvQ-shift of (ii) (:5509-5567): for each
place `v`, an endomorphism of the local space -- multiplication by `pvQ` --
whose effect on the local measure is the constant `pvQ ^ e_v`; this is the
avatar of [AbsTopIII], Proposition 5.7, (i), (b), at the place `v`. -/
structure PvQScalingDatum (pvQ : ℝ) where
  mul : ∀ v, D.M v → D.M v
  exponent : D.V → ℤ
  scale : ∀ v (S : Set (D.M v)), MeasurableSet S →
    volume (mul v '' S) = ENNReal.ofReal (pvQ ^ exponent v) * volume S

/-- **Q2** (Remark 3.1.1, (ii), :5559-5567 in the form displayed at
:5509-5567): with the normalized weights `1/N_v`, multiplying the
`v`-portions by `pvQ` changes the normalized weighted log-volume by
`(sum_v (1/N_v) e_v) * log pvQ`.  The coefficient equality to a prescribed
degree `d` is the named supply card below. -/
theorem shift_pvQ_add_log (pvQ : ℝ) (hpvQ : 0 < pvQ)
    (sc : D.PvQScalingDatum pvQ) (d : ℤ)
    (hdeg : ∑ v, (D.cardinality v : ℝ)⁻¹ * (sc.exponent v : ℝ) = (d : ℝ))
    (S : ∀ v, Set (D.M v)) (hS : D.IsDirectProductRegion S) :
    D.normalizedWeightedLogVolume (fun v => sc.mul v '' S v)
      = D.normalizedWeightedLogVolume S + (d : ℝ) * Real.log pvQ := by
  classical
  have hplace : ∀ v, Real.log ((volume (sc.mul v '' S v)).toReal)
      = Real.log ((volume (S v)).toReal)
        + (sc.exponent v : ℝ) * Real.log pvQ := by
    intro v
    have hscale := sc.scale v (S v) (hS v).1
    have hpz : (0 : ℝ) < pvQ ^ sc.exponent v := zpow_pos hpvQ _
    rw [hscale, ENNReal.toReal_mul, ENNReal.toReal_ofReal hpz.le]
    rw [Real.log_mul (zpow_ne_zero _ (ne_of_gt hpvQ))
      (ne_of_gt (ENNReal.toReal_pos (hS v).2.1 (hS v).2.2))]
    rw [Real.log_zpow]
    ring
  simp only [normalizedWeightedLogVolume]
  simp_rw [hplace]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul, hdeg]

/-- The `+log pvQ` case of (ii): the normalization coefficient is `+1`
(non-arithmetic archimedean side of the sign convention). -/
theorem shift_pvQ_add_log_of_coeff_one (pvQ : ℝ) (hpvQ : 0 < pvQ)
    (sc : D.PvQScalingDatum pvQ)
    (hdeg : ∑ v, (D.cardinality v : ℝ)⁻¹ * (sc.exponent v : ℝ) = 1)
    (S : ∀ v, Set (D.M v)) (hS : D.IsDirectProductRegion S) :
    D.normalizedWeightedLogVolume (fun v => sc.mul v '' S v)
      = D.normalizedWeightedLogVolume S + Real.log pvQ := by
  have h := D.shift_pvQ_add_log pvQ hpvQ sc 1 (by rw [hdeg]; norm_num) S hS
  simpa using h

/-- The `-log pvQ` case of (ii): the normalization coefficient is `-1`
(arithmetic side of the sign convention). -/
theorem shift_pvQ_sub_log_of_coeff_neg_one (pvQ : ℝ) (hpvQ : 0 < pvQ)
    (sc : D.PvQScalingDatum pvQ)
    (hdeg : ∑ v, (D.cardinality v : ℝ)⁻¹ * (sc.exponent v : ℝ) = -1)
    (S : ∀ v, Set (D.M v)) (hS : D.IsDirectProductRegion S) :
    D.normalizedWeightedLogVolume (fun v => sc.mul v '' S v)
      = D.normalizedWeightedLogVolume S - Real.log pvQ := by
  rw [sub_eq_add_neg]
  have h := D.shift_pvQ_add_log pvQ hpvQ sc (-1) (by rw [hdeg]; norm_num) S hS
  simpa using h

namespace Witness

/-- A concrete two-factor carrier: `V = Fin 2`, both local spaces `R` with
Lebesgue measure, both cardinalities `2`, factor region `[0,1]`; it inhabits
the direct product region hypotheses and shows the interface is
non-vacuous. -/
abbrev realCarrier : EWeightedLogVolumeData :=
  { V := Fin 2
    fintypeV := inferInstance
    nonemptyV := inferInstance
    M := fun _ => ℝ
    measureSpaceM := fun _ => inferInstance
    cardinality := fun _ => 2
    cardinality_pos := fun _ => by norm_num }

theorem realCarrier_totalCardinality : realCarrier.totalCardinality = 4 := by
  show (∏ _v : Fin 2, 2) = 4
  norm_num [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem realCarrier_kappa : realCarrier.kappa = (4 : ℝ)⁻¹ := by
  rw [kappa, realCarrier_totalCardinality]
  norm_num

/-- Q1 instantiated on the concrete two-factor carrier. -/
theorem realCarrier_kappa_log_eWeightedVolume_eq_weightedSum :
    realCarrier.kappa * Real.log
        ((realCarrier.eWeightedVolume
          (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1)).toReal)
      = realCarrier.normalizedWeightedLogVolume (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1) :=
  realCarrier.kappa_log_eWeightedVolume_eq_weightedSum
    (fun _ => inferInstance)
    (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1)
    (fun _ => ⟨measurableSet_Icc, by simp [Real.volume_Icc], by simp [Real.volume_Icc]⟩)

end Witness

end EWeightedLogVolumeData

end EWeightedLogVolume

namespace Audit

/-- Frozen interface card (no supplier claimed): the arithmetic instance of
the (iv) construction for the degree data of (ii). -/
def sourceEWeightedMeasureRealization : Obligation :=
  { id := "IUT-III.source-E-weighted-measure-realization"
    source :=
      "IUT III, Remark 3.1.1, (ii)-(iv) (pagewise plain text :5509-5567, " ++
        ":5568-5603, :5634-5746; display at :5739-5746)"
    status := VerificationStatus.interface
    note :=
      "Source-side identity demanded: on direct product regions, the " ++
        "weighted log-volumes of (ii) are kappa * log(muE) of the (iv) " ++
        "construction for the data (V, E, M) with the arithmetic degree " ++
        "cardinalities (N_v = [Kv:(Fmod)v] for the summand weights and " ++
        "[(Fmod)w:QvQ] for the fibers; tensor version with not necessarily " ++
        "distinct labels. No supplier is constructed: the identification of " ++
        "the local measure spaces and of the cardinalities with the degree " ++
        "factors is exactly the missing supply. Consumers: " ++
        "normalizedLogVolume_ind3Lift_add (SourceK1K2CardReduction.lean:194), " ++
        "certificate hull wiring (CertificateHullWiring.lean:247), " ++
        "card HULLREAL."
    dependsOn := [] }

/-- Frozen interface card (no supplier claimed): the degree-exponent
normalization behind the sign statement of (ii) (:5559-5567). -/
def sourcePvQShiftExponentNormalization : Obligation :=
  { id := "IUT-III.source-pvQ-shift-exponent-normalization"
    source :=
      "IUT III, Remark 3.1.1, (ii) (:5509-5567); [AbsTopIII], " ++
        "Proposition 5.7, (i), (b) (scaling law of the local volume)"
    status := VerificationStatus.interface
    note :=
      "Source-side identity demanded: with N_v the degree cardinalities of " ++
        "(ii) (tensor form prod_alpha [Kv_alpha:(Fmod)v_alpha]) and e_v the " ++
        "exponents of the pvQ-scaling of the local volumes (AbsTopIII " ++
        "5.7(i)(b) avatar), the normalized sum satisfies " ++
        "sum_v (1/N_v) e_v = +1 on the non-arithmetic archimedean side and " ++
        "= -1 on the arithmetic side (this is the content of the " ++
        "phrase: normalized so that multiplication by pvQ changes " ++
        "log-volumes by plus or minus log(pvQ)). No supplier is " ++
        "constructed; the local-volume scaling objects of AbsTopIII 5.7 " ++
        "are not among the frozen interfaces. Consumers: the shift " ++
        "corollaries of SourceEWeightedLogVolumeData."
    dependsOn := [] }

/-- File-level card for the E2 normalization skeleton. -/
def sourceEWeightedLogVolumeData : Obligation :=
  { id := "IUT-III.source-E-weighted-log-volume-data"
    source :=
      "IUT III, Remark 3.1.1, (ii)-(iv) (:5509-5746); " ++
        "wild-brainstorm-20261017 sections 23.E (E2) and 25 (S4)"
    status := VerificationStatus.interface
    note :=
      "Kernel-checked skeleton of the (ii)-(iv) normalization for the " ++
        "canonical cardinality construction: dimensionless data " ++
        "EWeightedLogVolumeData; the (iv) box computation " ++
        "(eWeightedVolume_apply); the display (Q1, " ++
        "kappa_log_eWeightedVolume_eq_weightedSum); the shift law (Q2, " ++
        "shift_pvQ_add_log with the +1/-1 specializations); and a concrete " ++
        "two-factor satisfiability witness. The source instantiation is " ++
        "split into the two supply cards above; the weighted sums are not " ++
        "presented as an additive measure on M_V (reduction point)."
    dependsOn :=
      ["IUT-III.source-E-weighted-measure-realization",
        "IUT-III.source-pvQ-shift-exponent-normalization"] }

end Audit

end LeanFormal.IUT
