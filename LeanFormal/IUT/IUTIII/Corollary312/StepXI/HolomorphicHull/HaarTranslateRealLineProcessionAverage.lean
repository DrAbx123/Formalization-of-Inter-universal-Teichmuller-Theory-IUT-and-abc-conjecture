import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HaarTranslateRealLineShellHomotopyRadialAngular

/-!
  # The procession-normalization layer: the finite-label uniform average on the
  real-line test carrier (outsider survey continuation: Corollary 3.12,
  procession-normalized mono-analytic log-volume; G5 two-layer accounting)

  ## Source quotes (corpus, OCR spacing and glyphs normalized)

  * [IUTchIII] Proposition 3.9, (i) (corpus :6889-6893):

      "when working with collections of capsules in a procession, as in
      Proposition 3.4, (ii), we obtain ... log-volumes on the products of the
      'M(-)' associated to the various capsules under consideration, which we
      normalize by taking the average, over the various capsules under
      consideration; we shall refer to this normalization as the
      procession-normalization"

  * [IUTchIII] Theorem B (corpus :1181-1188): the procession-normalized
    mono-analytic log-volume is defined "[where the average is taken over
    j in F_l^times -- cf. Remark 3.1.1, (ii), (iii), (iv); Proposition 3.9,
    (i), (ii); Theorem 3.11, (i), (a), for more details] of the holomorphic
    hull [cf. Remark 3.9.5, (i)] of the union of the possible images of a
    Theta-pilot object".

  * [IUTchIII] Remark 3.9.3 (corpus :7132-7150): more general weighted
    averages are impossible -- compatibility with the inclusion morphisms of
    the procession forces one "to assign the same weights" to the capsules;
    the average in the usual sense is the forced normalization.

  * [IUTchIII] discussion of the averages over j in F_l^times (corpus
    :10735-10742): "the averages over j in F_l^times that appear in the
    definition of the procession-normalized volumes involved may be thought
    of as a consequence of the F_l^times-symmetry acting on the labels of
    the theta values"; and (corpus :11535-11539): the procession-normalized
    volumes obtained by taking averages over j in F_l^times "[cf. Corollary
    3.12]" correspond "to the operation of dividing by p".

  ## Minimal fragment

  `realLineProcessionAverage` is the finite-label uniform average of a
  real-valued label family -- the test-carrier model of the averaging step
  of the procession-normalization, with the label set F_l^times (and the
  capsule index set of a procession) modeled by an arbitrary finite type
  `J` and the (forced equal) weights normalized to the average `1/#J`.
  Its algebraic laws: label-independence (`_const`), additivity (`_add`),
  negation (`_neg`), differences (`_sub`), scalar extraction (`_smul`, the
  shape of the "dividing by p" operation of :11535-11539), preservation of
  the zero point (`_zero_of_zero`), the translation law (`_add_const`), and
  invariance under relabeling (`_comp_equiv`, the label-symmetry face of
  :10735-10742).

  Two consumer bridges instantiate the laws at the section 17/18 objects:
  the procession average of the (label-independent) log-homotopy step of
  `realLineLogShellHomotopySystem` is the step weight `dot-mu-log(c)`
  itself (`realLineProcessionAverage_logShellStep`: the averaging layer is
  compatible with the packet layer, the two-layer accounting of G5), and
  the procession average of the unit log-shell log-volume is the zero point
  `mu-log(O) = 0` (`realLineProcessionAverage_unitLogShell_zero`).

  ## Annotations

  * proved: every declaration below;
  * reduced: the label set F_l^times (respectively, the collection of
    capsules of a procession) is modeled by an arbitrary finite type `J`
    with the uniform weight `1/#J` (Remark 3.9.3 forces equal weights; the
    average normalizes them); no group structure of F_l^times is used; the
    averaged quantities are the real-line test-carrier log-volumes of
    sections 15/17/18; the "dividing by p" correspondence is modeled only
    through the scalar-extraction law `_smul`;
  * additional data (not available on this carrier): the procession of
    capsules with its inclusion morphisms, the F_l^times-symmetry acting
    on theta value labels, the multiradial representation with the
    indeterminacies (Ind1)-(Ind3), and the literal arithmetic log-volumes.

  Evidence: `tmp/outsider-survey-iq-carrier-20261016/` logs and the landing
  report `logs/coordination/iq-hull-haar-logshell-landing-20261016.md`,
  section 19.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.HaarTranslateModel.RealLine

noncomputable section

/-! ## 1. The finite-label uniform average -/

/-- The procession average of a real-valued family over a finite label set:
the uniform average `(sum over j of w j) / #J` -- the test-carrier model of
the averaging step of the procession-normalization of [IUTchIII] Proposition
3.9, (i) (corpus :6889-6893) and of the average "taken over j in F_l^times"
of Theorem B (corpus :1181-1188). Reduction: the label set F_l^times (and the
capsule index set of a procession) is modeled by an arbitrary finite type `J`
with the uniform weight `1/#J`; by Remark 3.9.3 (corpus :7132-7150) the
weights are forced to be equal, and the average in the usual sense is the
normalized instance. -/
def realLineProcessionAverage {J : Type*} [Fintype J] (w : J → ℝ) : ℝ :=
  (∑ j, w j) / (Fintype.card J : ℝ)

/-- A label-independent family is unchanged by the procession average: the
average of a constant family over a nonempty finite label set is that
constant -- the compatibility of the averaging layer with the packet layer
(sections 17/18), i.e., procession normalization acts trivially on quantities
that do not depend on the label. -/
theorem realLineProcessionAverage_const {J : Type*} [Fintype J] [Nonempty J]
    (a : ℝ) : realLineProcessionAverage (fun _ : J => a) = a := by
  have hk : (Fintype.card J : ℝ) ≠ 0 := by
    have hpos : (0 : ℝ) < (Fintype.card J : ℝ) := by
      exact_mod_cast Fintype.card_pos
    exact ne_of_gt hpos
  unfold realLineProcessionAverage
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_div_cancel_left₀ a hk

/-- Additivity of the procession average in the label family. -/
theorem realLineProcessionAverage_add {J : Type*} [Fintype J] (w₁ w₂ : J → ℝ) :
    realLineProcessionAverage (fun j => w₁ j + w₂ j) =
      realLineProcessionAverage w₁ + realLineProcessionAverage w₂ := by
  unfold realLineProcessionAverage
  rw [Finset.sum_add_distrib, add_div]

/-- Negation law of the procession average. -/
theorem realLineProcessionAverage_neg {J : Type*} [Fintype J] (w : J → ℝ) :
    realLineProcessionAverage (fun j => -w j) = -realLineProcessionAverage w := by
  unfold realLineProcessionAverage
  rw [Finset.sum_neg_distrib, neg_div]

/-- Difference law of the procession average (the shape of averaged
consecutive-label increments). -/
theorem realLineProcessionAverage_sub {J : Type*} [Fintype J] (w₁ w₂ : J → ℝ) :
    realLineProcessionAverage (fun j => w₁ j - w₂ j) =
      realLineProcessionAverage w₁ - realLineProcessionAverage w₂ := by
  have h₁ : (fun j : J => w₁ j - w₂ j) = fun j : J => w₁ j + -w₂ j := by
    funext j
    exact sub_eq_add_neg (w₁ j) (w₂ j)
  rw [h₁, realLineProcessionAverage_add, realLineProcessionAverage_neg,
    sub_eq_add_neg]

/-- Scalar extraction for the procession average: a common multiplicative
factor comes out -- the shape of the "operation of dividing by p" of corpus
:11535-11539 realized through the uniform coefficient `1/#J` of the
average. -/
theorem realLineProcessionAverage_smul {J : Type*} [Fintype J] (c : ℝ)
    (w : J → ℝ) :
    realLineProcessionAverage (fun j => c * w j) =
      c * realLineProcessionAverage w := by
  unfold realLineProcessionAverage
  rw [← Finset.mul_sum]
  exact mul_div_assoc c (∑ j, w j) (Fintype.card J : ℝ)

/-- The zero point is preserved by the procession average: if every label
carries the value zero, then so does the average -- the `mu-log(O) = 0`
normalization (section 18, `realLineLogShellLogVolume_unit_zero`) survives
the averaging layer. -/
theorem realLineProcessionAverage_zero_of_zero {J : Type*} [Fintype J]
    (w : J → ℝ) (h : ∀ j, w j = 0) : realLineProcessionAverage w = 0 := by
  have hw : w = fun _ : J => (0 : ℝ) := funext h
  rw [hw, realLineProcessionAverage]
  simp

/-- Translation law of the procession average: adding a common constant to
every label shifts the average by that constant. -/
theorem realLineProcessionAverage_add_const {J : Type*} [Fintype J] [Nonempty J]
    (w : J → ℝ) (s : ℝ) :
    realLineProcessionAverage (fun j => w j + s) =
      realLineProcessionAverage w + s := by
  rw [realLineProcessionAverage_add w (fun _ : J => s),
    realLineProcessionAverage_const (J := J) s]

/-- Relabeling invariance of the procession average: the average does not
depend on the naming of the labels -- the label-symmetry face of the
F_l^times-average (corpus :10735-10742). -/
theorem realLineProcessionAverage_comp_equiv {J K : Type*} [Fintype J] [Fintype K]
    (e : J ≃ K) (w : K → ℝ) :
    realLineProcessionAverage (fun j => w (e j)) = realLineProcessionAverage w := by
  unfold realLineProcessionAverage
  rw [Equiv.sum_comp e w, Fintype.card_congr e]

/-! ## 2. Consumer bridges to the section 17/18 log-volume layer -/

/-- Two-layer compatibility (G5): the procession average of the
label-independent log-homotopy step of the shell-homotopy system of section
18 is the step weight `dot-mu-log(c)` itself -- averaging over the procession
does not disturb the packet-layer step computation. -/
theorem realLineProcessionAverage_logShellStep (c : ℝ) (hc : 0 < c) (n : ℤ)
    (J : Type*) [Fintype J] [Nonempty J] :
    realLineProcessionAverage (fun _ : J =>
      (realLineLogShellHomotopySystem c hc).logVolumeAt (n + 1) -
        (realLineLogShellHomotopySystem c hc).logVolumeAt n) =
      realLineDilationLogWeight c := by
  rw [realLineLogShellHomotopySystem_compatibility c hc n]
  exact realLineProcessionAverage_const (J := J) (realLineDilationLogWeight c)

/-- The procession average of the unit log-shell log-volume is the zero point
`mu-log(O) = 0` of section 18: the packet-layer zero point survives the
procession normalization. -/
theorem realLineProcessionAverage_unitLogShell_zero (J : Type*) [Fintype J] :
    realLineProcessionAverage (fun _ : J =>
      Real.log (normalizedRealLineVolume unitInterval).toReal) = 0 :=
  realLineProcessionAverage_zero_of_zero
    (fun _ : J => Real.log (normalizedRealLineVolume unitInterval).toReal)
    (fun _ => realLineLogShellLogVolume_unit_zero)

end

end LeanFormal.IUT.HaarTranslateModel.RealLine

namespace LeanFormal.IUT.Audit

/-- Audit record for the procession-normalization layer (finite-label uniform
average) on the real-line test carrier (outsider survey continuation:
[IUTchIII] Corollary 3.12, procession-normalized mono-analytic log-volume;
Proposition 3.9, (i), corpus :6889-6893; Theorem B, corpus :1181-1188;
Remark 3.9.3, corpus :7132-7150; averages over j in F_l^times, corpus
:10735-10742 and :11535-11539). -/
def haarTranslateRealLineProcessionAverage : Obligation :=
  { id := "IUT-III.corollary-3.12-haar-translate-real-line-procession-average"
    source :=
      "IUT III, Corollary 3.12, Step (xi); procession-normalized mono-analytic " ++
        "log-volume (Proposition 3.9, (i), corpus :6889-6893; Theorem B, " ++
        "corpus :1181-1188; Remark 3.9.3, corpus :7132-7150); averages over " ++
        "j in F_l^times (corpus :10735-10742, :11535-11539) -- test-carrier " ++
        "fragment"
    status := VerificationStatus.testCarrier
    note :=
      "Procession-normalization layer: the finite-label uniform average " ++
        "realLineProcessionAverage (sum over labels divided by the label " ++
        "count) with its algebraic laws -- label-independence " ++
        "(realLineProcessionAverage_const), additivity (_add), negation " ++
        "(_neg), differences (_sub), scalar extraction (_smul), preservation " ++
        "of the zero point (_zero_of_zero), translation (_add_const), and " ++
        "relabeling invariance (_comp_equiv) -- together with the consumer " ++
        "bridges to the section 17/18 log-volume layer " ++
        "(realLineProcessionAverage_logShellStep: the average of the " ++
        "label-independent log-homotopy step is the step weight " ++
        "dot-mu-log(c); realLineProcessionAverage_unitLogShell_zero: the " ++
        "average of the unit log-shell log-volume is zero, G5 two-layer " ++
        "accounting). Reduced: the label set F_l^times (respectively, the " ++
        "collection of capsules of a procession) is modeled by an arbitrary " ++
        "finite type with the uniform weight 1/#J (Remark 3.9.3 forces equal " ++
        "weights; the average normalizes them); no group structure; the " ++
        "averaged quantities are the real-line test-carrier log-volumes of " ++
        "sections 15/17/18; the dividing-by-p correspondence only through " ++
        "_smul. Additional data (not available): the procession of capsules " ++
        "with inclusion morphisms, the F_l^times-symmetry on theta value " ++
        "labels, the multiradial representation with indeterminacies " ++
        "(Ind1)-(Ind3), and the literal arithmetic log-volumes."
    dependsOn :=
      [ "IUT-III.corollary-3.12-haar-translate-real-line-shell-homotopy-radial-angular" ] }

end LeanFormal.IUT.Audit
