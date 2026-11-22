import tmp.sheaf.xif.paper.S2441C9PaperCarrierActual
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.PowerBasis

/-!
# S2450: general paper normalization on the actual S1895 q-pilot data

This file continues the general-normalization package of S2441/S2448 on the
actual S1895 paper input.  It builds the fixed-Type bad-place map, the IUT-IV
root factor, the global degree normalization 1/[F:Q], and the paper-normalized
degree/magnitude/scalar, and then decides the naive identification with the raw
source scalar.

## What is actual here

* `S2450BadPlaceMap` is a fixed-Type structure: at every bad place it records
  the actual base prime `b.1.maximalIdeal`, the actual q-parameter
  `paperQV D b`, its actual completed-DVR order `paperQVOrder D b`, and the
  actual residue weight `Real.log 5`, together with the corresponding equality
  fields.  `s2450BadPlaceMap` inhabits it definitionally, and the map is tied
  to the actual S1968 divisor weight via `paperBadBasePlace_weight`.

* `paperRootFactor l = (2 * l.value)⁻¹` is the IUT-IV root factor
  (IUT IV, p. 23: `|log(q)| = (1/(2l)) log(q)`), with the algebraic inverse
  lemma `paperRootFactor_mul_two_l` and the reassociation lemmas used below.

* `gaussianField_finrank_two` proves `Module.finrank ℚ GaussianField = 2`
  from `GaussianField = AdjoinRoot (X² + 1)` using
  `AdjoinRoot.powerBasis` and `PowerBasis.finrank` (not the nonexistent
  `AdjoinRoot.finrank`).  `paperFmod_finrank_two` transports it to
  `PaperFmod D`.

* `paperNormalizedDegree`, `paperNormalizedMagnitude`, and
  `paperNormalizedSignedLog` implement the paper formula

    `- |log q| = - (2l)⁻¹ * (1/[F:Q]) * deg_F(q^□_ADiv)`

  from IUT IV, Definition 1.9, and p. 23.  The actual formula is
  `paperNormalizedSignedLog_eq_paper_formula`; the concrete S1487/S1527
  evaluation is `paperNormalizedSignedLog_eq`.

## The naive identification is false; exact missing structure

The project's `sourceQPilotSignedLog` is the raw, unnormalized bad-family sum
`-Σ_b |log q_b|` (see its own docstring in `PaperQPilotObject`).  The paper
scalar is the normalized one above.  On the concrete S1895 data the raw sum is
`-C` with `C = S1487Cand.order * log 5 > 0`, while the paper scalar is
`-C/(4l)`.  These are unequal because `l ≥ 5`:

  `sourceQPilotSignedLog_ne_paperNormalizedSignedLog`.

Consequently there is no inhabitant of the exact missing structure
`S2450GeneralNormalizationRequired`, which records the naive equality; this is
proved as `s2450GeneralNormalizationRequired_impossible`.  The corrected
actual scalar is the paper formula, not the raw source sum.

The local completion weights and the procession average of
`ProcessionNormalizationWeightsActual` are not used in the q-pilot global
scalar: the q-pilot normalization is the global factor `(2l)⁻¹ * (1/[F:Q])`
times the residue weights `log(#k_v)`.  The procession average is a separate
target (S2451).

No placeholder proof, custom assumption, True/PUnit slot, arbitrary inhabitant
or assumption-only gate is used.  The exact missing structure is not inhabited;
indeed it is shown to be impossible.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.XiFPaper.S1927GlobalFrobenioidLogShellActual
open LeanFormal.IUT.XiFPaper.S1960QPilotAnchorActual
open LeanFormal.IUT.XiFPaper.S1968QVDeterminedQPilotActual
open LeanFormal.IUT.XiFPaper.S1979QPilotStripFromDivisorActual
open LeanFormal.IUT.XiFPaper.S2441C9PaperCarrierActual
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual
open LeanFormal.IUT.XiFPaper.S1527OOrderEqualityActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.IUTIV.Estimates
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open IsDedekindDomain NumberField

local instance s2450GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance s2450FivePrime : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

namespace LeanFormal.IUT.XiFPaper.S2450GeneralNormalizationActual

/-! ## 1. The actual fixed-Type bad-place map -/

/-- Fixed-Type bad-place data for the S1895 paper input: the actual base prime,
the actual q-parameter, its actual completed-DVR order, and the actual residue
weight `log 5`, with equality fields.  All fields are actual data; there are no
Prop-valued identification slots beyond the displayed equalities. -/
structure S2450BadPlaceMap (D : S1895PaperInput) where
  /-- the actual base Fmod prime of the bad place -/
  place : (paperInput D).initial.badPlaces →
    HeightOneSpectrum (NumberField.RingOfIntegers (PaperFmod D))
  /-- it is the maximal ideal of the bad finite place -/
  place_eq : ∀ b, place b = b.1.maximalIdeal
  /-- the actual Definition 3.1(b)(c) q-parameter -/
  q_v : (paperInput D).initial.badPlaces → ℝ
  /-- it is `paperQV D b` -/
  q_v_eq : ∀ b, q_v b = paperQV D b
  /-- the actual completed-DVR order of the q-parameter -/
  order : (paperInput D).initial.badPlaces → ℕ
  /-- it is `paperQVOrder D b` -/
  order_eq : ∀ b, order b = paperQVOrder D b
  /-- the actual residue weight of the bad base prime -/
  residueWeight : (paperInput D).initial.badPlaces → ℝ
  /-- it is `log 5` -/
  residueWeight_eq : ∀ b, residueWeight b = Real.log 5

/-- The actual fixed-Type bad-place map. -/
noncomputable def s2450BadPlaceMap (D : S1895PaperInput) :
    S2450BadPlaceMap D where
  place := fun b => b.1.maximalIdeal
  place_eq := fun _ => rfl
  q_v := paperQV D
  q_v_eq := fun _ => rfl
  order := paperQVOrder D
  order_eq := fun _ => rfl
  residueWeight := fun _ => Real.log 5
  residueWeight_eq := fun _ => rfl

@[simp] theorem s2450BadPlaceMap_place (D : S1895PaperInput)
    (b : (paperInput D).initial.badPlaces) :
    (s2450BadPlaceMap D).place b = b.1.maximalIdeal := rfl

@[simp] theorem s2450BadPlaceMap_place_paperBadBasePlace (D : S1895PaperInput)
    (b : (paperInput D).initial.badPlaces) :
    (s2450BadPlaceMap D).place b = paperBadBasePlace D b := rfl

@[simp] theorem s2450BadPlaceMap_q_v (D : S1895PaperInput)
    (b : (paperInput D).initial.badPlaces) :
    (s2450BadPlaceMap D).q_v b = paperQV D b := rfl

@[simp] theorem s2450BadPlaceMap_order (D : S1895PaperInput)
    (b : (paperInput D).initial.badPlaces) :
    (s2450BadPlaceMap D).order b = paperQVOrder D b := rfl

@[simp] theorem s2450BadPlaceMap_residueWeight (D : S1895PaperInput)
    (b : (paperInput D).initial.badPlaces) :
    (s2450BadPlaceMap D).residueWeight b = Real.log 5 := rfl

/-- The bad q-parameter is nonzero. -/
theorem s2450BadPlaceMap_q_v_ne_zero (D : S1895PaperInput)
    (b : (paperInput D).initial.badPlaces) :
    (s2450BadPlaceMap D).q_v b ≠ 0 := by
  rw [s2450BadPlaceMap_q_v]
  exact paperQV_ne_zero D b

/-- The bad q-parameter is contracting, so its log is negative. -/
theorem s2450BadPlaceMap_q_v_log_neg (D : S1895PaperInput)
    (b : (paperInput D).initial.badPlaces) :
    Real.log ((s2450BadPlaceMap D).q_v b) < 0 := by
  rw [s2450BadPlaceMap_q_v]
  exact paperQV_log_neg' D b

/-- The completed-DVR order is positive. -/
theorem s2450BadPlaceMap_order_pos (D : S1895PaperInput)
    (b : (paperInput D).initial.badPlaces) :
    0 < (s2450BadPlaceMap D).order b := by
  rw [s2450BadPlaceMap_order]
  exact paperQVOrder_pos D b

/-- The residue weight is positive. -/
theorem s2450BadPlaceMap_residueWeight_pos (D : S1895PaperInput)
    (b : (paperInput D).initial.badPlaces) :
    0 < (s2450BadPlaceMap D).residueWeight b := by
  rw [s2450BadPlaceMap_residueWeight]
  exact Real.log_pos (by norm_num)

/-- The residue weight is exactly the IUT-IV weight of the recorded base
place. -/
theorem s2450BadPlaceMap_residueWeight_eq_weight (D : S1895PaperInput)
    (b : (paperInput D).initial.badPlaces) :
    (s2450BadPlaceMap D).residueWeight b =
      IUTIVPlace.weight (PaperFmod D)
        (IUTIVPlace.finite ((s2450BadPlaceMap D).place b)) := by
  rw [s2450BadPlaceMap_residueWeight, s2450BadPlaceMap_place_paperBadBasePlace]
  exact (paperBadBasePlace_weight D b).symm

/-- The q_v-determined order identity: the absolute log of the q-parameter is
the order times the residue weight `log 5`. -/
theorem s2450BadPlaceMap_abs_log_q_v_eq_order_mul_residueWeight
    (D : S1895PaperInput) (b : (paperInput D).initial.badPlaces) :
    |Real.log ((s2450BadPlaceMap D).q_v b)| =
      ((s2450BadPlaceMap D).order b : ℝ) *
        (s2450BadPlaceMap D).residueWeight b := by
  rw [s2450BadPlaceMap_q_v, s2450BadPlaceMap_order,
    s2450BadPlaceMap_residueWeight]
  exact paperQVOrder_abs_log D b

/-! ## 2. The IUT-IV root factor (2l)⁻¹ -/

/-- The IUT-IV root factor 1/(2l) (IUT IV, p. 23). -/
noncomputable def paperRootFactor (l : PrimeGeFive) : ℝ :=
  (2 * (l.value : ℝ))⁻¹

/-- The root factor as a division. -/
theorem paperRootFactor_eq_inv (l : PrimeGeFive) :
    paperRootFactor l = 1 / (2 * (l.value : ℝ)) := by
  rw [paperRootFactor, one_div]

/-- The defining algebra lemma: (2l)⁻¹ * (2l) = 1. -/
theorem paperRootFactor_mul_two_l (l : PrimeGeFive) :
    paperRootFactor l * (2 * (l.value : ℝ)) = 1 := by
  unfold paperRootFactor
  have hl : (l.value : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.Prime.ne_zero l.prime)
  have h2l : (2 : ℝ) * (l.value : ℝ) ≠ 0 :=
    mul_ne_zero (by norm_num) hl
  exact inv_mul_cancel₀ h2l

/-- The commuted algebra lemma. -/
theorem two_l_mul_paperRootFactor (l : PrimeGeFive) :
    (2 * (l.value : ℝ)) * paperRootFactor l = 1 := by
  rw [mul_comm (2 * (l.value : ℝ)) (paperRootFactor l)]
  exact paperRootFactor_mul_two_l l

/-- The root factor is positive. -/
theorem paperRootFactor_pos (l : PrimeGeFive) : 0 < paperRootFactor l := by
  unfold paperRootFactor
  have hl : (0 : ℝ) < (l.value : ℝ) := by
    exact_mod_cast (Nat.Prime.pos l.prime)
  exact inv_pos.mpr (mul_pos (by norm_num) hl)

/-- The root factor is nonzero. -/
theorem paperRootFactor_ne_zero (l : PrimeGeFive) : paperRootFactor l ≠ 0 :=
  ne_of_gt (paperRootFactor_pos l)

/-- Reassociation with an explicit 1/2: (2l)⁻¹ * 2⁻¹ = (4l)⁻¹. -/
theorem paperRootFactor_mul_inv_two (l : PrimeGeFive) :
    paperRootFactor l * (2 : ℝ)⁻¹ = (4 * (l.value : ℝ))⁻¹ := by
  unfold paperRootFactor
  rw [← mul_inv]
  congr 1
  ring

/-- Division form: (2l)⁻¹ * (x/2) = x/(4l). -/
theorem paperRootFactor_mul_div_two (l : PrimeGeFive) (x : ℝ) :
    paperRootFactor l * (x / 2) = x / (4 * (l.value : ℝ)) := by
  unfold paperRootFactor
  simp only [div_eq_mul_inv]
  calc
    (2 * (l.value : ℝ))⁻¹ * (x * 2⁻¹)
        = ((2 * (l.value : ℝ))⁻¹ * 2⁻¹) * x := by ring
    _ = (4 * (l.value : ℝ))⁻¹ * x := by
        rw [← mul_inv]
        rw [show (2 * (l.value : ℝ)) * 2 = 4 * (l.value : ℝ) by ring]
    _ = x * (4 * (l.value : ℝ))⁻¹ := by ring
    _ = x / (4 * (l.value : ℝ)) := by rw [div_eq_mul_inv]

/-! ## 3. The global degree normalization 1/[F:Q] -/

/-- The concrete Gaussian field is the AdjoinRoot model used in the tree. -/
theorem gaussianField_finrank_two : Module.finrank ℚ GaussianField = 2 := by
  let f : Polynomial ℚ := Polynomial.X ^ 2 - Polynomial.C (-1)
  have hf : f ≠ 0 := by
    intro h
    have h0 : f.natDegree = 0 := by rw [h, Polynomial.natDegree_zero]
    have h2 : f.natDegree = 2 := by
      dsimp [f]
      exact Polynomial.natDegree_X_pow_sub_C
    rw [h2] at h0
    exact (by norm_num : (2 : ℕ) ≠ 0) h0
  let pb : PowerBasis ℚ (AdjoinRoot f) := AdjoinRoot.powerBasis hf
  have hfr : Module.finrank ℚ (AdjoinRoot f) = pb.dim := PowerBasis.finrank pb
  change Module.finrank ℚ (AdjoinRoot f) = 2
  rw [hfr]
  show f.natDegree = 2
  dsimp [f]
  exact Polynomial.natDegree_X_pow_sub_C

/-- The paper base field is the concrete Gaussian field. -/
theorem paperFmod_eq_gaussianField (D : S1895PaperInput) :
    PaperFmod D = GaussianField := by
  have hinit : (paperInput D).initial =
      S1527SourceData D.l D.R D.redCompat D.hredCompat D.torCompat D.htorCompat
        D.orbCompat D.horbCompat D.secCompat D.hsecCompat D.cusCompat D.hcusCompat := rfl
  change (paperInput D).initial.arithmetic.Fmod = GaussianField
  rw [hinit]
  change (S1280SourceData_of_remaining D.l D.R D.redCompat D.hredCompat
    D.torCompat D.htorCompat D.orbCompat D.horbCompat D.secCompat D.hsecCompat
    D.cusCompat D.hcusCompat).arithmetic.Fmod = GaussianField
  rw [S1280SourceData_of_remaining_arithmetic]
  rfl

/-- The paper base field has degree two over Q: [F:Q] = 2. -/
theorem paperFmod_finrank_two (D : S1895PaperInput) :
    Module.finrank ℚ (PaperFmod D) = 2 := by
  change Module.finrank ℚ GaussianField = 2
  exact gaussianField_finrank_two

/-! ## 4. Normalized degree, magnitude, and signed log -/

/-- The normalized degree of the actual q-pilot divisor (IUT IV, Definition
1.9): (1/[F:Q]) * deg_F(q^□_ADiv). -/
noncomputable def paperNormalizedDegree (D : S1895PaperInput) : ℝ :=
  ((Module.finrank ℚ (PaperFmod D) : ℝ))⁻¹ *
    IUTIVArithmeticDivisor.deg (F := PaperFmod D) (paperQPilotDivisor D)

/-- The paper-normalized magnitude |log q| = (1/(2l)) * deg(q^□_ADiv), where
deg(q^□_ADiv) is the normalized degree. -/
noncomputable def paperNormalizedMagnitude (D : S1895PaperInput) : ℝ :=
  paperRootFactor D.l * paperNormalizedDegree D

/-- The paper-normalized signed log-volume -|log q|. -/
noncomputable def paperNormalizedSignedLog (D : S1895PaperInput) : ℝ :=
  - paperNormalizedMagnitude D

/-- The normalized degree is the existing IUT-IV ndeg. -/
theorem paperNormalizedDegree_eq_ndeg (D : S1895PaperInput) :
    paperNormalizedDegree D =
      IUTIVArithmeticDivisor.ndeg (F := PaperFmod D) (paperQPilotDivisor D) :=
  (IUTIVArithmeticDivisor.ndeg_apply (F := PaperFmod D)
    (D := paperQPilotDivisor D)).symm

/-- The paper formula for the normalized signed log, in explicit
rootFactor * (1/[F:Q]) * deg_F form. -/
theorem paperNormalizedSignedLog_eq_paper_formula (D : S1895PaperInput) :
    paperNormalizedSignedLog D =
      - (paperRootFactor D.l *
        (((Module.finrank ℚ (PaperFmod D) : ℝ))⁻¹ *
          IUTIVArithmeticDivisor.deg (F := PaperFmod D) (paperQPilotDivisor D))) :=
  rfl

/-- The actual normalized degree is half of the raw q-pilot degree. -/
theorem paperNormalizedDegree_eq (D : S1895PaperInput) :
    paperNormalizedDegree D =
      ((S1487Cand.order : ℝ) * Real.log 5) / 2 := by
  unfold paperNormalizedDegree
  rw [paperFmod_finrank_two, s2441_concrete_divisor_deg]
  rw [div_eq_mul_inv]
  ring

/-- The actual paper magnitude is C/(4l) with C = order_C3 * log 5. -/
theorem paperNormalizedMagnitude_eq (D : S1895PaperInput) :
    paperNormalizedMagnitude D =
      ((S1487Cand.order : ℝ) * Real.log 5) / (4 * (D.l.value : ℝ)) := by
  unfold paperNormalizedMagnitude
  rw [paperNormalizedDegree_eq]
  exact paperRootFactor_mul_div_two D.l _

/-- The actual paper signed log-volume is -C/(4l). -/
theorem paperNormalizedSignedLog_eq (D : S1895PaperInput) :
    paperNormalizedSignedLog D =
      -(((S1487Cand.order : ℝ) * Real.log 5) / (4 * (D.l.value : ℝ))) := by
  unfold paperNormalizedSignedLog
  exact congrArg Neg.neg (paperNormalizedMagnitude_eq D)

/-- The paper magnitude is positive. -/
theorem paperNormalizedMagnitude_pos (D : S1895PaperInput) :
    0 < paperNormalizedMagnitude D := by
  rw [paperNormalizedMagnitude_eq]
  have hlog : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have horder : 0 < (S1487Cand.order : ℝ) := by
    exact_mod_cast S1487Cand.order_pos
  have hlpos : (0 : ℝ) < (D.l.value : ℝ) := by
    exact_mod_cast (Nat.Prime.pos D.l.prime)
  have h4l : (0 : ℝ) < 4 * (D.l.value : ℝ) :=
    mul_pos (by norm_num) hlpos
  exact div_pos (mul_pos horder hlog) h4l

/-- The paper signed log-volume is negative. -/
theorem paperNormalizedSignedLog_neg (D : S1895PaperInput) :
    paperNormalizedSignedLog D < 0 := by
  unfold paperNormalizedSignedLog
  linarith [paperNormalizedMagnitude_pos D]

/-! ## 5. The naive equality with the raw source sum is false -/

/-- The raw source q-pilot sum is not the paper-normalized signed log-volume:
the paper scalar is -C/(4l), while the raw sum is -C, and C > 0, l >= 5. -/
theorem sourceQPilotSignedLog_ne_paperNormalizedSignedLog
    (D : S1895PaperInput) :
    sourceQPilotSignedLog (paperInput D).initial ≠
      paperNormalizedSignedLog D := by
  rw [s2441_concrete_normalization D, paperNormalizedSignedLog_eq]
  intro h
  have hdiv :
      ((S1487Cand.order : ℝ) * Real.log 5) =
        ((S1487Cand.order : ℝ) * Real.log 5) /
          (4 * (D.l.value : ℝ)) := by
    linarith
  have hlog : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have horder : 0 < (S1487Cand.order : ℝ) := by
    exact_mod_cast S1487Cand.order_pos
  have hC : 0 < (S1487Cand.order : ℝ) * Real.log 5 :=
    mul_pos horder hlog
  have hlpos : (0 : ℝ) < (D.l.value : ℝ) := by
    exact_mod_cast (Nat.Prime.pos D.l.prime)
  have h4l : (0 : ℝ) < 4 * (D.l.value : ℝ) :=
    mul_pos (by norm_num) hlpos
  have hd : (4 * (D.l.value : ℝ)) ≠ 0 := ne_of_gt h4l
  have hmul :
      ((S1487Cand.order : ℝ) * Real.log 5) =
        ((S1487Cand.order : ℝ) * Real.log 5) *
          (4 * (D.l.value : ℝ)) :=
    (div_eq_iff hd).mp hdiv.symm
  have hcancel : (1 : ℝ) = 4 * (D.l.value : ℝ) := by
    apply mul_left_cancel₀ (ne_of_gt hC)
    rw [mul_one]
    exact hmul
  have h5 : (5 : ℝ) ≤ (D.l.value : ℝ) := by
    exact_mod_cast D.l.ge_five
  linarith

/-- The paper-normalized signed log-volume is not the raw source sum. -/
theorem paperNormalizedSignedLog_ne_sourceQPilotSignedLog
    (D : S1895PaperInput) :
    paperNormalizedSignedLog D ≠
      sourceQPilotSignedLog (paperInput D).initial :=
  fun h => sourceQPilotSignedLog_ne_paperNormalizedSignedLog D h.symm

/-- The exact naive general-normalization requirement: the raw source q-pilot
sum equals the paper-normalized scalar.  The structure records the actual
bad-place map, the root factor, the finrank normalization, the normalized
degree and magnitude, and the equality that the paper normalization would have
to satisfy.  It has no inhabitant; indeed it is impossible for the concrete
S1895 data. -/
structure S2450GeneralNormalizationRequired (D : S1895PaperInput) where
  /-- the actual fixed-Type bad-place map -/
  badPlaceMap : S2450BadPlaceMap D
  /-- the IUT-IV root factor -/
  rootFactor : ℝ
  rootFactor_eq : rootFactor = paperRootFactor D.l
  /-- the global degree normalization -/
  finrank_eq_two : Module.finrank ℚ (PaperFmod D) = 2
  /-- the normalized degree (1/[F:Q]) * deg_F -/
  normalizedDegree : ℝ
  normalizedDegree_eq : normalizedDegree = paperNormalizedDegree D
  /-- the paper magnitude (2l)⁻¹ * normalizedDegree -/
  normalizedMagnitude : ℝ
  normalizedMagnitude_eq : normalizedMagnitude = paperNormalizedMagnitude D
  /-- the paper signed scalar -/
  paperNormalized : ℝ
  paperNormalized_eq : paperNormalized = - normalizedMagnitude
  /-- the naive identification with the raw source scalar -/
  candidate_eq_paper :
    sourceQPilotSignedLog (paperInput D).initial = paperNormalized

/-- The exact naive general-normalization structure has no inhabitant: the raw
source sum and the paper-normalized scalar differ by the actual factor 4l. -/
theorem s2450GeneralNormalizationRequired_impossible
    (D : S1895PaperInput) :
    ¬ Nonempty (S2450GeneralNormalizationRequired D) := by
  rintro ⟨h⟩
  have hpaper : h.paperNormalized = paperNormalizedSignedLog D := by
    calc
      h.paperNormalized = - h.normalizedMagnitude := h.paperNormalized_eq
      _ = - paperNormalizedMagnitude D := by rw [h.normalizedMagnitude_eq]
      _ = paperNormalizedSignedLog D := rfl
  exact sourceQPilotSignedLog_ne_paperNormalizedSignedLog D
    (h.candidate_eq_paper.trans hpaper)

/-! ## 6. Interface checks (not run in this file; serial no-compile policy) -/

#check S2450BadPlaceMap
#check s2450BadPlaceMap
#check s2450BadPlaceMap_abs_log_q_v_eq_order_mul_residueWeight
#check paperRootFactor
#check paperRootFactor_mul_two_l
#check gaussianField_finrank_two
#check paperFmod_finrank_two
#check paperNormalizedDegree
#check paperNormalizedMagnitude
#check paperNormalizedSignedLog
#check paperNormalizedSignedLog_eq
#check sourceQPilotSignedLog_ne_paperNormalizedSignedLog
#check S2450GeneralNormalizationRequired
#check s2450GeneralNormalizationRequired_impossible

end LeanFormal.IUT.XiFPaper.S2450GeneralNormalizationActual
end
