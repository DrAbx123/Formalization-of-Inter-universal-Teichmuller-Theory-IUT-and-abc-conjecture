import tmp.sheaf.xif.paper.S1903SignedHullActual
import tmp.sheaf.xif.paper.S1904ProcessionBridgeActual
import tmp.sheaf.xif.paper.S1915ThetaHullA0Actual

/-!
# S1930: comparison of the S1903 actual determinant average with the S1915 a0

Layer: **O** (original-text Theta-link / Step (xi-f), procession normalization).

## The two quantities

The S1903 actual determinant is built from the actual Gaussian source theta
packet

  thetaScale l j = q ^ (j ^ 2),   q = gaussianFiveThetaQ = 1/5,

by the geometric determinant normalization M = card(SignedLabel l.value) ^ 3.
Its procession is the uniform SignedLabel procession (card = l.value labels,
including 0 and both signs) with weight 1/card, and its average is

  s1904ProcessionAverage (s1903ActualDeterminant l)
    = -thetaLogVolume l / (M * card)
    = log 5 * (l.value ^ 2 - 1) / (12 * l.value ^ 3).          (S1903/S1917)

The S1915 actual theta hull is the S1902 root-extension product hull; its Haar
readout is

  s1915A0 T = max 0 (1 + sum_b [K_b : Q_p] * log (rootImageRadius T b)),

where b ranges over the actual bad places and the radii are the actual S1902
root-image radii.  S1915 proves that the S1904 procession bridge is exactly

  s1904ProcessionAverage P = s1915A0 T.

## What this file proves (no fake)

1. The exact closed form of the S1903 average (as a function of l only), and
   its positivity.
2. The exact comparison theorem: the bridge at the S1903 determinant is
   equivalent to the scalar equation

     s1915ClosedForm T = s1930S1903Average l,

   equivalently s1915A0 T = s1930S1903Average l.  This is a theorem, not an
   assumption.
3. A genuine obstruction on the normalization side: the paper procession
   normalization (S694: l* positive labels j = 1,...,l*, weight 1/l*) applied
   to the *same* S1903 root packet gives

     s1930PaperLStarAverage l
       = (l.value / (l.value - 1)) * s1930S1903Average l,

   which is strictly larger than the uniform SignedLabel average for every
   l >= 5.  Hence the S1903 determinant is **not** the source determinant
   determined by the paper's l* procession normalization; it is off by the
   explicit nonzero label-count factor l/(l-1).
4. The exact first missing is named:

     S1930SourceNormalization T : s1915ClosedForm T = s1930S1903Average l.

   The bridge is equivalent to it.  This file does **not** assert it.  It is
   the source-normalization identification between the actual S1902/The S1915
   bad-place hull readout and the Gaussian S1903 determinant normalization.
5. A conditional non-equality: when the unclipped S1915 closed form is
   nonpositive, s1915A0 T = 0 while s1930S1903Average l > 0, so the two sides
   are provably unequal and the bridge fails at the S1903 determinant.

## Exact source-normalization missing (paper side)

The paper's procession normalization is not the uniform SignedLabel average:
IUT II Remark 4.7.3 and IUT III Theorem B/Corollary 3.12 average over the l*
classes j in F_l^x / {+-1}, with weight 1/l*, and the paper object is
hull-first: one first takes the least lambda-O hull of the possible Theta
images and then the normalized Haar log-volume (S797/S764).  Consequently the
source determinant must be built from the *actual bad-place theta data*
(the S1902/S1915 root-extension hull radii and degrees), with the l*
procession, and normalized so that its average is exactly the S1915 Haar
readout a0.  The S1903 determinant uses a different source packet (the
Gaussian q = 1/5 packet), a different label set (all SignedLabels, including
0 and both signs), a different weight (1/l), and a different determinant
normalization (M = l^3).  The equation in (4) is precisely the missing
identification between these two normalizations.  This file proves the exact
comparison and the l* obstruction; it neither fakes the identification nor
asserts a false equality.

No sorry, axiom, True/PUnit slot, arbitrary datum, or fake log-volume is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1930CompareA0AverageActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ConcreteSourceEtaleThetaBridge
open LeanFormal.IUT.XiFPaper.S1903SignedHullActual
open LeanFormal.IUT.XiFPaper.S1904ProcessionBridgeActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open scoped BigOperators

variable {l : PrimeGeFive}

/-! ## 1. The label arithmetic and the theta magnitude -/

/-- The zero signed label. -/
def s1930ZeroLabel (l : PrimeGeFive) : SignedLabel l.value :=
  ⟨0, by
    have hstar : (0 : Int) <= (lStar l.value : Int) := by
      exact_mod_cast Nat.zero_le (lStar l.value)
    constructor <;> omega⟩

@[simp] theorem s1930ZeroLabel_val (l : PrimeGeFive) :
    (s1930ZeroLabel l).1 = 0 := rfl

/-- The positive paper label j = i+1, i = 0,...,l*-1. -/
def s1930PositiveLabel (l : PrimeGeFive) (i : Fin (lStar l.value)) :
    SignedLabel l.value :=
  ⟨(i.1 : Int) + 1, by
    constructor
    · have h0 : (0 : Int) <= (i.1 : Int) := by exact_mod_cast Nat.zero_le i.1
      omega
    · have hi : i.1 + 1 <= lStar l.value := Nat.succ_le_of_lt i.2
      exact_mod_cast hi⟩

@[simp] theorem s1930PositiveLabel_val (l : PrimeGeFive)
    (i : Fin (lStar l.value)) :
    (s1930PositiveLabel l i).1 = (i.1 : Int) + 1 := rfl

theorem s1930PositiveLabel_pos (l : PrimeGeFive)
    (i : Fin (lStar l.value)) :
    0 < (s1930PositiveLabel l i).1 := by
  rw [s1930PositiveLabel_val]
  have h : (0 : Int) <= (i.1 : Int) := by exact_mod_cast Nat.zero_le i.1
  omega

theorem s1930PositiveLabel_injective (l : PrimeGeFive) :
    Function.Injective (s1930PositiveLabel l) := by
  intro i j h
  have h' : (i.1 : Int) + 1 = (j.1 : Int) + 1 := by
    simpa using congrArg Subtype.val h
  have h'' : (i.1 : Int) = (j.1 : Int) := by omega
  exact Fin.ext (by exact_mod_cast h'')

theorem s1930PositiveLabel_surjective (l : PrimeGeFive)
    (j : SignedLabel l.value) (hj : 0 < j.1) :
    ∃ i : Fin (lStar l.value), s1930PositiveLabel l i = j := by
  have hjnonneg : (0 : Int) <= j.1 := le_of_lt hj
  have hjn : ((j.1.toNat : Int)) = j.1 := Int.toNat_of_nonneg hjnonneg
  have hjposnat : 0 < j.1.toNat := by omega
  have hjle : j.1.toNat <= lStar l.value := by
    have hle : j.1 <= (lStar l.value : Int) := j.2.2
    omega
  let i : Fin (lStar l.value) := ⟨j.1.toNat - 1, by omega⟩
  refine ⟨i, ?_⟩
  apply Subtype.ext
  rw [s1930PositiveLabel_val]
  change (i.1 : Int) + 1 = j.1
  have hi : (i.1 : Int) = (j.1.toNat : Int) - 1 := by
    change ((j.1.toNat - 1 : Nat) : Int) = (j.1.toNat : Int) - 1
    omega
  rw [hi, hjn]
  ring

/-- The positive-filter sum is the l* positive-label sum. -/
theorem s1930PositiveFilter_sum_eq (l : PrimeGeFive)
    (f : SignedLabel l.value -> Real) :
    (∑ j ∈ (Finset.univ.filter (fun j : SignedLabel l.value => 0 < j.1)), f j) =
      ∑ i : Fin (lStar l.value), f (s1930PositiveLabel l i) := by
  classical
  symm
  refine Finset.sum_bij (fun i _ => s1930PositiveLabel l i) ?_ ?_ ?_ ?_
  · intro i _
    simp [s1930PositiveLabel_pos]
  · intro i _ j _ h
    exact s1930PositiveLabel_injective l h
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    obtain ⟨i, hi⟩ := s1930PositiveLabel_surjective l j hj
    exact ⟨i, Finset.mem_univ i, hi⟩
  · intro i _
    rfl

/-- The negative-filter sum equals the positive-filter sum for an even
function (the involution j -> -j). -/
theorem s1930NegativeFilter_sum_eq (l : PrimeGeFive)
    (f : SignedLabel l.value -> Real)
    (hf : ∀ j : SignedLabel l.value, f (SignedLabel.neg j) = f j) :
    (∑ j ∈ (Finset.univ.filter (fun j : SignedLabel l.value => j.1 < 0)), f j) =
      ∑ j ∈ (Finset.univ.filter (fun j : SignedLabel l.value => 0 < j.1)), f j := by
  classical
  refine Finset.sum_bij (fun j _ => SignedLabel.neg j) ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    simp [SignedLabel.neg_val]
    omega
  · intro a ha b hb h
    have h' : SignedLabel.neg a = SignedLabel.neg b := h
    calc
      a = SignedLabel.neg (SignedLabel.neg a) := (SignedLabel.neg_involutive a).symm
      _ = SignedLabel.neg (SignedLabel.neg b) := congrArg SignedLabel.neg h'
      _ = b := SignedLabel.neg_involutive b
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    refine ⟨SignedLabel.neg j, ?_, SignedLabel.neg_involutive j⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simpa using hj
  · intro j _
    exact (hf j).symm

/-- The zero-filter sum is the value at the zero label. -/
theorem s1930ZeroFilter_sum_eq (l : PrimeGeFive)
    (f : SignedLabel l.value -> Real) :
    (∑ j ∈ (Finset.univ.filter (fun j : SignedLabel l.value => j.1 = 0)), f j) =
      f (s1930ZeroLabel l) := by
  classical
  have hset : (Finset.univ.filter (fun j : SignedLabel l.value => j.1 = 0)) =
      {s1930ZeroLabel l} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hj
      apply Subtype.ext
      simpa using hj
    · intro hj
      rw [hj]
      rfl
  rw [hset, Finset.sum_singleton]

/-- Split a signed-label sum into zero, positive, and negative parts. -/
theorem s1930Sum_split (l : PrimeGeFive) (f : SignedLabel l.value -> Real) :
    (∑ j : SignedLabel l.value, f j) =
      f (s1930ZeroLabel l) +
        (∑ j ∈ (Finset.univ.filter (fun j : SignedLabel l.value => 0 < j.1)), f j) +
        (∑ j ∈ (Finset.univ.filter (fun j : SignedLabel l.value => j.1 < 0)), f j) := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (s := (Finset.univ : Finset (SignedLabel l.value)))
    (p := fun j => j.1 = 0) (f := f)
  have hnonzero : (Finset.univ.filter (fun j : SignedLabel l.value => ¬ j.1 = 0)) =
      (Finset.univ.filter (fun j : SignedLabel l.value => 0 < j.1)) ∪
        (Finset.univ.filter (fun j : SignedLabel l.value => j.1 < 0)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro hj
      by_cases hpos : 0 < j.1
      · exact Or.inl hpos
      · exact Or.inr (by omega)
    · intro h
      rcases h with hp | hn
      · omega
      · omega
  have hdisj : Disjoint
      (Finset.univ.filter (fun j : SignedLabel l.value => 0 < j.1))
      (Finset.univ.filter (fun j : SignedLabel l.value => j.1 < 0)) := by
    rw [Finset.disjoint_left]
    intro j hp hn
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hn
    omega
  have hzero := s1930ZeroFilter_sum_eq l f
  calc
    (∑ j : SignedLabel l.value, f j) =
        (∑ j ∈ (Finset.univ.filter (fun j : SignedLabel l.value => j.1 = 0)), f j) +
          (∑ j ∈ (Finset.univ.filter (fun j : SignedLabel l.value => ¬ j.1 = 0)), f j) :=
        hsplit.symm
    _ = (∑ j ∈ (Finset.univ.filter (fun j : SignedLabel l.value => j.1 = 0)), f j) +
          ((∑ j ∈ (Finset.univ.filter (fun j : SignedLabel l.value => 0 < j.1)), f j) +
            (∑ j ∈ (Finset.univ.filter (fun j : SignedLabel l.value => j.1 < 0)), f j)) := by
          rw [hnonzero, Finset.sum_union hdisj]
    _ = f (s1930ZeroLabel l) +
          (∑ j ∈ (Finset.univ.filter (fun j : SignedLabel l.value => 0 < j.1)), f j) +
          (∑ j ∈ (Finset.univ.filter (fun j : SignedLabel l.value => j.1 < 0)), f j) := by
          rw [hzero]
          ring

/-- For an even function vanishing at 0, the signed-label sum is twice the
positive-label sum. -/
theorem s1930_signedSum_eq_zero_add_two_mul_pos (l : PrimeGeFive)
    (f : SignedLabel l.value -> Real)
    (hf : ∀ j, f (SignedLabel.neg j) = f j)
    (h0 : f (s1930ZeroLabel l) = 0) :
    (∑ j : SignedLabel l.value, f j) =
      2 * (∑ i : Fin (lStar l.value), f (s1930PositiveLabel l i)) := by
  rw [s1930Sum_split l f, h0,
    s1930PositiveFilter_sum_eq l f,
    s1930NegativeFilter_sum_eq l f hf,
    s1930PositiveFilter_sum_eq l f]
  ring

/-- The positive magnitude -log(thetaScale j) of the actual theta packet. -/
noncomputable def s1930ThetaMagnitude (l : PrimeGeFive)
    (j : SignedLabel l.value) : Real :=
  -thetaLogScale l j

theorem s1930ThetaMagnitude_neg (l : PrimeGeFive) (j : SignedLabel l.value) :
    s1930ThetaMagnitude l (SignedLabel.neg j) = s1930ThetaMagnitude l j := by
  unfold s1930ThetaMagnitude
  change -Real.log (thetaScale l (SignedLabel.neg j)) =
    -Real.log (thetaScale l j)
  rw [theta_scale_neg]

theorem s1930ThetaMagnitude_zero (l : PrimeGeFive) :
    s1930ThetaMagnitude l (s1930ZeroLabel l) = 0 := by
  unfold s1930ThetaMagnitude
  have h : thetaScale l (s1930ZeroLabel l) = 1 := by
    rw [theta_scale_eq_real_value]
    change realThetaValue LeanFormal.IUT.gaussianFiveThetaQ 0 = 1
    rw [realThetaValue_zero]
  change -Real.log (thetaScale l (s1930ZeroLabel l)) = 0
  rw [h, Real.log_one, neg_zero]

theorem s1930_sum_magnitude_eq_neg_thetaLogVolume (l : PrimeGeFive) :
    (∑ j : SignedLabel l.value, s1930ThetaMagnitude l j) =
      -thetaLogVolume l := by
  unfold s1930ThetaMagnitude
  rw [theta_log_volume_eq_sum, ← Finset.sum_neg_distrib]

theorem s1930_signedMagnitudeSum_eq_two_mul_pos (l : PrimeGeFive) :
    (∑ j : SignedLabel l.value, s1930ThetaMagnitude l j) =
      2 * (∑ i : Fin (lStar l.value),
        s1930ThetaMagnitude l (s1930PositiveLabel l i)) :=
  s1930_signedSum_eq_zero_add_two_mul_pos l (s1930ThetaMagnitude l)
    (s1930ThetaMagnitude_neg l) (s1930ThetaMagnitude_zero l)

theorem s1930_two_mul_lStar_add_one (l : PrimeGeFive) :
    2 * lStar l.value + 1 = l.value := by
  unfold lStar
  rcases l.odd with ⟨k, hk⟩
  omega

/-- The actual theta log-scale in the Gaussian q = 1/5 form. -/
theorem s1930_thetaLogScale_eq_neg_log_five_mul (l : PrimeGeFive)
    (j : SignedLabel l.value) :
    thetaLogScale l j =
      -((gaussExponent j.1).toNat : Real) * Real.log 5 := by
  rw [theta_log_scale_eq,
    LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceTheaterCarrier.gaussianFiveThetaQ_eq_inv_five,
    Real.log_inv]
  ring

/-- The finite square-sum identity on the n = l* labels. -/
theorem s1930_sum_range_sq_succ (n : Nat) :
    (∑ i ∈ Finset.range n, ((i + 1 : Real)^2)) =
      (n : Real) * (n + 1) * (2 * n + 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- The l*-label second moment: sum of (i+1)^2 is l(l^2-1)/24. -/
theorem s1930_sum_sq_paperLabel (l : PrimeGeFive) :
    (∑ i : Fin (lStar l.value), ((i.1 + 1 : Real)^2)) =
      (l.value : Real) * ((l.value : Real)^2 - 1) / 24 := by
  rw [Fin.sum_univ_eq_sum_range (fun i : Nat => ((i + 1 : Real)^2))]
  rw [s1930_sum_range_sq_succ]
  have h2 : (2 * (lStar l.value : Real) + 1) = (l.value : Real) := by
    exact_mod_cast s1930_two_mul_lStar_add_one l
  have hn : (lStar l.value : Real) = ((l.value : Real) - 1) / 2 := by
    linarith
  rw [hn]
  ring

/-- The signed-label Gauss-exponent sum. -/
theorem s1930_gaussSum_eq (l : PrimeGeFive) :
    (∑ j : SignedLabel l.value, ((gaussExponent j.1).toNat : Real)) =
      (l.value : Real) * ((l.value : Real)^2 - 1) / 12 := by
  have hpair := s1930_signedSum_eq_zero_add_two_mul_pos l
    (fun j => ((gaussExponent j.1).toNat : Real))
    (by intro j; simp [SignedLabel.neg])
    (by simp [s1930ZeroLabel, gaussExponent])
  have hterm : ∀ i : Fin (lStar l.value),
      ((gaussExponent (s1930PositiveLabel l i).1).toNat : Real) =
        ((i.1 + 1 : Real)^2) := by
    intro i
    have hcast : (s1930PositiveLabel l i).1 = ((i.1 + 1 : Nat) : Int) := by
      rw [s1930PositiveLabel_val]
      push_cast
      ring
    rw [hcast]
    unfold gaussExponent
    rw [← Int.natCast_pow, Int.toNat_natCast]
    norm_num
  rw [hpair]
  calc
    2 * (∑ i : Fin (lStar l.value),
        ((gaussExponent (s1930PositiveLabel l i).1).toNat : Real)) =
        2 * (∑ i : Fin (lStar l.value), ((i.1 + 1 : Real)^2)) := by
          congr 1
          exact Finset.sum_congr rfl (fun i _ => hterm i)
    _ = 2 * ((l.value : Real) * ((l.value : Real)^2 - 1) / 24) := by
          rw [s1930_sum_sq_paperLabel]
    _ = (l.value : Real) * ((l.value : Real)^2 - 1) / 12 := by ring

/-- The actual theta log-volume in the Gaussian q = 1/5 form. -/
theorem s1930_thetaLogVolume_eq (l : PrimeGeFive) :
    thetaLogVolume l =
      -Real.log 5 * ((l.value : Real) * ((l.value : Real)^2 - 1) / 12) := by
  rw [theta_log_volume_eq_sum]
  have hpoint : ∀ j : SignedLabel l.value,
      thetaLogScale l j =
        -((gaussExponent j.1).toNat : Real) * Real.log 5 :=
    s1930_thetaLogScale_eq_neg_log_five_mul l
  calc
    (∑ j : SignedLabel l.value, thetaLogScale l j) =
        ∑ j : SignedLabel l.value,
          -((gaussExponent j.1).toNat : Real) * Real.log 5 := by
          exact Finset.sum_congr rfl (fun j _ => hpoint j)
    _ = ∑ j : SignedLabel l.value,
          -(((gaussExponent j.1).toNat : Real) * Real.log 5) := by
          exact Finset.sum_congr rfl (fun j _ => by ring)
    _ = -(∑ j : SignedLabel l.value,
          ((gaussExponent j.1).toNat : Real) * Real.log 5) := by
          rw [Finset.sum_neg_distrib]
    _ = -((∑ j : SignedLabel l.value,
          ((gaussExponent j.1).toNat : Real)) * Real.log 5) := by
          rw [Finset.sum_mul]
    _ = -(Real.log 5) *
          (∑ j : SignedLabel l.value, ((gaussExponent j.1).toNat : Real)) := by
          ring
    _ = -(Real.log 5) *
          ((l.value : Real) * ((l.value : Real)^2 - 1) / 12) := by
          rw [s1930_gaussSum_eq]
    _ = -Real.log 5 * ((l.value : Real) * ((l.value : Real)^2 - 1) / 12) := by
          ring


/-! ## 2. The S1903 average: exact formula and positivity -/

/-- The S1903 actual determinant's procession average, named. -/
noncomputable def s1930S1903Average (l : PrimeGeFive) : Real :=
  s1904ProcessionAverage (s1903ActualDeterminant l)

/-- The exact average of the S1903 determinant. -/
theorem s1930S1903Average_eq (l : PrimeGeFive) :
    s1930S1903Average l =
      -thetaLogVolume l /
        ((s1903TensorPower l : Real) *
          (Fintype.card (SignedLabel l.value) : Real)) := by
  unfold s1930S1903Average s1904ProcessionAverage
  exact s1903ActualDeterminant_processionNormalizedLogVolume l

/-- The same average with the signed-label cardinality evaluated as l. -/
theorem s1930S1903Average_eq_card (l : PrimeGeFive) :
    s1930S1903Average l =
      -thetaLogVolume l /
        ((l.value : Real) ^ 3 * (l.value : Real)) := by
  rw [s1930S1903Average_eq, SignedLabel.card_signedLabel]
  unfold s1903TensorPower
  rw [SignedLabel.card_signedLabel]
  norm_num

/-- The exact log5 closed form of the S1903 average. -/
theorem s1930S1903Average_eq_log5 (l : PrimeGeFive) :
    s1930S1903Average l =
      Real.log 5 * ((l.value : Real)^2 - 1) / (12 * (l.value : Real)^3) := by
  rw [s1930S1903Average_eq_card, s1930_thetaLogVolume_eq]
  have hl : (l.value : Real) ≠ 0 := by
    exact_mod_cast l.prime.ne_zero
  field_simp [hl]


/-- The S1903 average is the uniform SignedLabel average of the positive
magnitudes divided by the geometric determinant power M. -/
theorem s1930S1903Average_eq_magnitudeAverage (l : PrimeGeFive) :
    s1930S1903Average l =
      (Fintype.card (SignedLabel l.value) : Real)⁻¹ *
        (∑ j : SignedLabel l.value,
          (s1930ThetaMagnitude l j / (s1903TensorPower l : Real))) := by
  have hM : (s1903TensorPower l : Real) ≠ 0 := by
    exact_mod_cast s1903TensorPower_ne_zero l
  have hcard : (Fintype.card (SignedLabel l.value) : Real) ≠ 0 := by
    have hpos : 0 < Fintype.card (SignedLabel l.value) :=
      Fintype.card_pos_iff.mpr
        ⟨SignedLabel.representative l (0 : Fl l.value)⟩
    exact_mod_cast (Nat.ne_of_gt hpos)
  rw [s1930S1903Average_eq, ← Finset.sum_div,
    s1930_sum_magnitude_eq_neg_thetaLogVolume]
  field_simp [hM, hcard]

theorem s1930S1903Average_pos (l : PrimeGeFive) :
    0 < s1930S1903Average l := by
  rw [s1930S1903Average_eq]
  have hvol : thetaLogVolume l < 0 := by
    rw [theta_log_volume_eq_sum]
    refine Finset.sum_neg' (fun j _ => ?_)
      ⟨s1903LabelOne l, Finset.mem_univ _, ?_⟩
    · exact s1903_thetaLogScale_nonpos l j
    · rw [thetaLogScale, s1903_thetaScale_labelOne l]
      exact Real.log_neg (by norm_num) (by norm_num)
  have hM : (0 : Real) < (s1903TensorPower l : Real) := by
    exact_mod_cast s1903TensorPower_pos l
  have hcard : (0 : Real) < (Fintype.card (SignedLabel l.value) : Real) := by
    have hpos : 0 < Fintype.card (SignedLabel l.value) :=
      Fintype.card_pos_iff.mpr
        ⟨SignedLabel.representative l (0 : Fl l.value)⟩
    exact_mod_cast hpos
  exact div_pos (neg_pos.mpr hvol) (mul_pos hM hcard)

/-! ## 3. The paper l*-procession normalization is not the S1903 one -/

/-- The paper's l*-label procession average of the same S1903 root-packet
values: positive labels only, weight 1/l*. -/
noncomputable def s1930PaperLStarAverage (l : PrimeGeFive) : Real :=
  (lStar l.value : Real)⁻¹ *
    (∑ i : Fin (lStar l.value),
      (s1930ThetaMagnitude l (s1930PositiveLabel l i) /
        (s1903TensorPower l : Real)))


theorem s1930_lStar_pos (l : PrimeGeFive) : 0 < lStar l.value := by
  have h5 := l.ge_five
  unfold lStar
  omega

/-- **The exact label-count discrepancy**: applying the paper's l* procession
normalization to the same root packet multiplies the S1903 uniform SignedLabel
average by l/(l-1). -/
theorem s1930PaperLStarAverage_eq_ratio (l : PrimeGeFive) :
    s1930PaperLStarAverage l =
      ((l.value : Real) / ((l.value : Real) - 1)) * s1930S1903Average l := by
  have hM : (s1903TensorPower l : Real) ≠ 0 := by
    exact_mod_cast s1903TensorPower_ne_zero l
  have hcard : (Fintype.card (SignedLabel l.value) : Real) = (l.value : Real) := by
    rw [SignedLabel.card_signedLabel]
  have hls : (lStar l.value : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (s1930_lStar_pos l))
  have hl : (l.value : Real) ≠ 0 := by
    exact_mod_cast l.prime.ne_zero
  have htwo : (2 * (lStar l.value : Real) + 1) = (l.value : Real) := by
    exact_mod_cast s1930_two_mul_lStar_add_one l
  have hsum : (∑ j : SignedLabel l.value, s1930ThetaMagnitude l j) =
      2 * (∑ i : Fin (lStar l.value),
        s1930ThetaMagnitude l (s1930PositiveLabel l i)) :=
    s1930_signedMagnitudeSum_eq_two_mul_pos l
  have hsumdiv : (∑ j : SignedLabel l.value,
        (s1930ThetaMagnitude l j / (s1903TensorPower l : Real))) =
      (∑ j : SignedLabel l.value, s1930ThetaMagnitude l j) /
        (s1903TensorPower l : Real) := by
    rw [Finset.sum_div]
  have hsumdivpos : (∑ i : Fin (lStar l.value),
        (s1930ThetaMagnitude l (s1930PositiveLabel l i) /
          (s1903TensorPower l : Real))) =
      (∑ i : Fin (lStar l.value),
        s1930ThetaMagnitude l (s1930PositiveLabel l i)) /
        (s1903TensorPower l : Real) := by
    rw [Finset.sum_div]
  have hA : s1930S1903Average l =
      (2 / ((l.value : Real) * (s1903TensorPower l : Real))) *
        (∑ i : Fin (lStar l.value),
          s1930ThetaMagnitude l (s1930PositiveLabel l i)) := by
    rw [s1930S1903Average_eq_magnitudeAverage, hsumdiv, hsum, hcard]
    field_simp [hM, hl]
  have hP : s1930PaperLStarAverage l =
      (1 / ((lStar l.value : Real) * (s1903TensorPower l : Real))) *
        (∑ i : Fin (lStar l.value),
          s1930ThetaMagnitude l (s1930PositiveLabel l i)) := by
    rw [s1930PaperLStarAverage, hsumdivpos]
    field_simp [hM, hls]
  have hsub : (l.value : Real) - 1 = 2 * (lStar l.value : Real) := by
    linarith
  rw [hA, hP, hsub]
  field_simp [hM, hls, hl, hsub]

/-- The paper l* normalization of the same packet is strictly larger than the
S1903 uniform SignedLabel average. -/
theorem s1930PaperLStarAverage_gt (l : PrimeGeFive) :
    s1930S1903Average l < s1930PaperLStarAverage l := by
  rw [s1930PaperLStarAverage_eq_ratio]
  have hA := s1930S1903Average_pos l
  have h5 : (5 : Real) <= (l.value : Real) := by exact_mod_cast l.ge_five
  have hden : (0 : Real) < (l.value : Real) - 1 := by linarith
  have hfactor : (1 : Real) < (l.value : Real) / ((l.value : Real) - 1) := by
    rw [one_lt_div hden]
    linarith
  calc
    s1930S1903Average l = 1 * s1930S1903Average l := by ring
    _ < ((l.value : Real) / ((l.value : Real) - 1)) * s1930S1903Average l :=
      mul_lt_mul_of_pos_right hfactor hA

theorem s1930PaperLStarAverage_ne (l : PrimeGeFive) :
    s1930PaperLStarAverage l ≠ s1930S1903Average l :=
  ne_of_gt (s1930PaperLStarAverage_gt l)

/-- The statement that the S1903 determinant is the paper-l*-normalized
determinant of its own packet.  It is false, by the strict factor l/(l-1). -/
def S1930PaperNormalizationOfS1903 (l : PrimeGeFive) : Prop :=
  s1930S1903Average l = s1930PaperLStarAverage l

theorem s1930PaperNormalizationOfS1903_false (l : PrimeGeFive) :
    ¬ S1930PaperNormalizationOfS1903 l :=
  fun h => s1930PaperLStarAverage_ne l h.symm

/-! ## 4. Comparison with the S1915 actual hull readout a0 -/

variable (T : LeanFormal.IUT.InitialThetaSource.SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The S1904 bridge at the S1903 determinant is exactly
s1903Average = a0. -/
theorem s1930_bridge_iff_average_eq_a0 :
    S1904ProcessionBridge (s1902ActualThetaHull T) (s1903ActualDeterminant l) ↔
      s1930S1903Average l = s1915A0 T := by
  rw [s1915_bridge_iff_average_eq_a0]
  rfl

/-- The exact scalar source-normalization equation left by the comparison:
the unclipped S1915 closed form equals the S1903 average. -/
def S1930SourceNormalization : Prop :=
  s1915ClosedForm T = s1930S1903Average l

/-- The scalar source-normalization equation is equivalent to
s1915A0 = s1903Average, because the S1903 average is positive. -/
theorem s1930SourceNormalization_iff_a0 :
    S1930SourceNormalization T ↔ s1915A0 T = s1930S1903Average l := by
  unfold S1930SourceNormalization
  rw [s1915_a0_eq_max T]
  have hA := s1930S1903Average_pos l
  constructor
  · intro h
    have hc : 0 < s1915ClosedForm T := by rw [h]; exact hA
    rw [max_eq_right (le_of_lt hc)]
    exact h
  · intro h
    by_cases hc : 0 ≤ s1915ClosedForm T
    · rw [max_eq_right hc] at h
      exact h
    · have hc' : s1915ClosedForm T ≤ 0 := le_of_lt (not_le.mp hc)
      rw [max_eq_left hc'] at h
      linarith

/-- **The exact comparison theorem**: the bridge at the S1903 determinant is
equivalent to the scalar source-normalization equation. -/
theorem s1930_bridge_iff_sourceNormalization :
    S1904ProcessionBridge (s1902ActualThetaHull T) (s1903ActualDeterminant l) ↔
      S1930SourceNormalization T := by
  constructor
  · intro h
    exact (s1930SourceNormalization_iff_a0 T).mpr
      ((s1930_bridge_iff_average_eq_a0 T).mp h).symm
  · intro h
    exact (s1930_bridge_iff_average_eq_a0 T).mpr
      ((s1930SourceNormalization_iff_a0 T).mp h).symm

/-- The same comparison in the original s1915A0 form. -/
theorem s1930_bridge_iff_closedForm :
    S1904ProcessionBridge (s1902ActualThetaHull T) (s1903ActualDeterminant l) ↔
      s1915ClosedForm T = s1930S1903Average l :=
  s1930_bridge_iff_sourceNormalization T

/-- **Conditional non-equality**: when the unclipped S1915 closed form is
nonpositive, the S1915 readout is 0 while the S1903 average is strictly
positive; hence the two sides are unequal and the bridge fails at the S1903
determinant. -/
theorem s1930_s1915A0_ne_s1903Average_of_closedForm_nonpos
    (h : s1915ClosedForm T ≤ 0) :
    s1915A0 T ≠ s1930S1903Average l := by
  rw [s1915_a0_eq_zero_of_closedForm_nonpos T h]
  exact ne_of_lt (s1930S1903Average_pos l)

/-- Under the same hypothesis, the S1904 bridge fails at the S1903
determinant. -/
theorem s1930_bridge_false_of_closedForm_nonpos
    (h : s1915ClosedForm T ≤ 0) :
    ¬ S1904ProcessionBridge (s1902ActualThetaHull T) (s1903ActualDeterminant l) := by
  intro hb
  exact s1930_s1915A0_ne_s1903Average_of_closedForm_nonpos T h
    ((s1930_bridge_iff_average_eq_a0 T).mp hb).symm

/-- The exact first missing, named: the source-normalization identification
between the actual S1902/S1915 bad-place hull readout and the Gaussian S1903
determinant normalization.  The file proves it is equivalent to the bridge but
does not assert it. -/
def S1930FirstMissing : Prop :=
  S1930SourceNormalization T

theorem s1930FirstMissing_iff_bridge :
    S1930FirstMissing T ↔
      S1904ProcessionBridge (s1902ActualThetaHull T)
        (s1903ActualDeterminant l) :=
  (s1930_bridge_iff_sourceNormalization T).symm

/-! ## 5. Axiom probes -/

#print axioms s1930S1903Average_eq
#print axioms s1930S1903Average_eq_log5
#print axioms s1930S1903Average_eq_card
#print axioms s1930S1903Average_eq_magnitudeAverage
#print axioms s1930S1903Average_pos
#print axioms s1930PaperLStarAverage_eq_ratio
#print axioms s1930PaperLStarAverage_gt
#print axioms s1930PaperNormalizationOfS1903_false
#print axioms s1930_bridge_iff_average_eq_a0
#print axioms s1930SourceNormalization_iff_a0
#print axioms s1930_bridge_iff_sourceNormalization
#print axioms s1930_s1915A0_ne_s1903Average_of_closedForm_nonpos
#print axioms s1930_bridge_false_of_closedForm_nonpos
#print axioms s1930FirstMissing_iff_bridge

end LeanFormal.IUT.XiFPaper.S1930CompareA0AverageActual

end