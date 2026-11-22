import tmp.sheaf.xif.paper.S1950ArchimedeanLogShellActual
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.MetricSpace.Basic

/-!
# S1954: the period-carrying (full paper) archimedean log-shell

## What the paper actually says

S1927/S1950 build a **reduced** `ArchimedeanLogShellDatum`: a compact convex set
`logShell` contained in the actual closed unit ball `{x | ‖x‖ ≤ 1}` of the
actual completion `w.Completion` and containing `0`.  S1950 states explicitly
that this is *not* the paper's archimedean log-shell: the period generator
`2*π*I`, the closed line segment whose endpoints differ by that period, the
orbit of that segment under the local units, and the log-link upper
semi-commutativity are all absent from the reduced shape.

The paper's archimedean model is concrete and explicit.  [IUTchIII],
Remark 1.2.2, (ii), with `k = K_v` a complex archimedean field, sets

  `O_k := {a ∈ k | |a| ≤ 1}`, `O_k^× := {a ∈ k | |a| = 1}`, `exp_k : k → k^×`,

and computes the log-shell of Definition 1.1, (ii), as

  `I_k := {a ∈ k | |a| ≤ π}`,

with the two properties (b^arc), (c^arc) of Proposition 1.2, (v):

  (b^arc)  `O_k^◃ = O_k \ {0} ⊆ O_k ⊆ I_k`,
  (c^arc)  `O_k^× ⊆ exp_k(I_k)`.

The abstract Definition 1.1, (ii), describes `I_k` as the `Ψ^×_{log(†F_v)}`-orbit
of the (unique) closed line segment preserved by multiplication by `±1` whose
endpoints differ by a generator of the kernel of `Ψ∼_{†F_v} ↠ Ψgp_{†F_v}`.
In the concrete complex model this is the segment `[-πi, πi]` (endpoint
difference `-πi + πi = 2πi`, the generator of `ker exp_k = 2πi Z`), and its
orbit under `O_k^×` is exactly the closed disk of radius `π`.  [IUTchIII],
Remark 3.9.4, (vi), records the companion fact that `O_k^× ⊆ k` has length
`2π`.

The "upper semi-commutativity" of the log-link ([IUTchIII], Remark 1.2.2,
(iii), (iv)) is exactly this pair of one-sided statements: at `v ∈ V^arc` it is
a *surjectivity* (`O_k^× ⊆ exp_k(I_k)`), not an equality, and (iv) records
that no "lower semi-commutativity" is available.  This file packages the
containments `O_k ⊆ I_k` and `O_k^× ⊆ exp_k(I_k)` as the
`logLink_upperSemi` data of the full datum, and proves the failure of the
reverse containment `exp_k(I_k) ⊆ I_k`.

## What this file constructs

`PaperArchimedeanLogShellDatum D w` is the full, period-carrying archimedean
log-shell datum: the log-shell itself, its compactness/convexity/membership of
`0`, the containment `O_k ⊆ I_k`, the period generator with its kernel
characterisation, the fundamental closed segment (endpoints differing by the
period, preserved by `±1`), the orbit identity
`I_k = O_k^× · (fundamental segment)`, and the log-link upper semi-commutativity
`O_k^× ⊆ exp_k(I_k)`.

For every `S1895PaperInput` `D` and every **complex** archimedean place `w` of
`Fmod`, `paperArchimedeanLogShellDatum D w hw` inhabits it with
`logShell = {x | ‖x‖ ≤ π}`, `period = 2πi`,
`fundamentalSegment = [-πi, πi]`.  All fields are proved from the actual
metric/topological data of `w.Completion`; no field is fitted.

## The exact first missing relative to S1927/S1950

1. **Normalization mismatch at complex places.**  The reduced S1927 shape
   demands `logShell ⊆ {‖x‖ ≤ 1}`.  No full paper datum can satisfy that at a
   complex place: the period is the difference of two points of the log-shell,
   so `‖period‖ ≤ 2` would follow from the unit-ball bound, while the actual
   period has `‖period‖ = 2π > 2` (`no_logShell_subset_unitBall`).  Hence
   S1950's closed unit ball can never be upgraded to the paper's log-shell: the
   missing ingredient is precisely the `π`-normalization
   (`I_k = {‖x‖ ≤ π}`, the closed unit ball of the `π`-normalized seminorm
   `x ↦ ‖x‖ / π`), not a proof obligation about the unit ball.

2. **Real versus complex archimedean places.**  The full datum requires a nonzero
   period, hence is *provably uninhabited* at a real place
   (`real_place_not_inhabited`): the period group of `exp_R` is trivial.  This
   matches [IUTchI], Definition 3.1, (a), which assumes `√-1 ∈ F` (so every
   archimedean place of an initial Θ-datum is complex) and [IUTchIII],
   Remark 1.2.2, (ii), which reads "Thus, `K_v` is a complex archimedean
   field".  It is a genuine hypothesis of the paper, not a proof gap; but it
   means that the "full" upgrade of S1927's `S1927FirstMissing` must be
   quantified over complex places.

No `sorry`, `admit`, `axiom`, `True`/`PUnit` slot, empty type or gate device is
used.  The only classical input is the case distinction
`w.IsComplex` versus `w.IsReal` and the argument choices in `Complex.arg`.
-/

noncomputable section

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.XiFPaper.S1927GlobalFrobenioidLogShellActual
open LeanFormal.IUT.XiFPaper.S1950ArchimedeanLogShellActual
open NumberField

namespace LeanFormal.IUT.XiFPaper.S1954ArchimedeanPeriodActual

variable (D : S1895PaperInput) (w : NumberField.InfinitePlace (PaperFmod D))

/-! ## 1. The archimedean local field: units, exponential, period -/

/-- The canonical ring isomorphism `w.Completion ≃+* C` at a complex place. -/
noncomputable abbrev completionRingEquivComplex (hw : w.IsComplex) : w.Completion ≃+* Complex :=
  NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw

/-- The canonical ring isomorphism `w.Completion ≃+* R` at a real place. -/
noncomputable abbrev completionRingEquivReal (hreal : w.IsReal) : w.Completion ≃+* Real :=
  NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hreal

/-- The compact unit group `O_k^× = {u | ‖u‖ = 1}` of the archimedean local
field, i.e. the metric unit sphere of the completion. -/
def archimedeanUnitSphere : Set w.Completion :=
  {u | ‖u‖ = 1}

/-- The exponential map of the archimedean local field: `Complex.exp` at a
complex place, `Real.exp` at a real place, both transported along the
canonical isometric field isomorphism. -/
noncomputable def archimedeanExp : w.Completion → w.Completion := by
  classical
  exact
    if hw : w.IsComplex then
      fun x => (completionRingEquivComplex D w hw).symm
        (Complex.exp ((completionRingEquivComplex D w hw) x))
    else
      let hreal : w.IsReal := NumberField.InfinitePlace.not_isComplex_iff_isReal.mp hw
      fun x => (completionRingEquivReal D w hreal).symm
        (Real.exp ((completionRingEquivReal D w hreal) x))

/-- The exponential map at a complex place, unfolded. -/
theorem archimedeanExp_of_isComplex (hw : w.IsComplex) (x : w.Completion) :
    archimedeanExp D w x =
      (completionRingEquivComplex D w hw).symm
        (Complex.exp ((completionRingEquivComplex D w hw) x)) := by
  classical
  rw [archimedeanExp]
  rw [dif_pos hw]

/-- The exponential map at a real place, unfolded. -/
theorem archimedeanExp_of_isReal (hreal : w.IsReal) (x : w.Completion) :
    archimedeanExp D w x =
      (completionRingEquivReal D w hreal).symm
        (Real.exp ((completionRingEquivReal D w hreal) x)) := by
  classical
  have hnc : ¬ w.IsComplex := NumberField.InfinitePlace.not_isComplex_iff_isReal.mpr hreal
  rw [archimedeanExp]
  rw [dif_neg hnc]

/-- The canonical isomorphism at a complex place is norm-preserving in the
inverse direction. -/
theorem norm_completionRingEquivComplex_symm (hw : w.IsComplex) (y : Complex) :
    ‖(completionRingEquivComplex D w hw).symm y‖ = ‖y‖ := by
  have h := ringEquivComplexOfIsComplex_norm D w hw
    ((completionRingEquivComplex D w hw).symm y)
  rw [RingEquiv.apply_symm_apply] at h
  exact h.symm

/-- The norm of an integer multiple in the completion, transported from `C`. -/
theorem norm_intCast_completion (hw : w.IsComplex) (n : ℤ) :
    ‖(n : w.Completion)‖ = |(n : Real)| := by
  have h1 : (completionRingEquivComplex D w hw) (n : w.Completion) = (n : Complex) :=
    map_intCast (completionRingEquivComplex D w hw) n
  have h2 : ‖(n : w.Completion)‖ = ‖(n : Complex)‖ := by
    rw [← h1, ringEquivComplexOfIsComplex_norm D w hw]
  rw [h2, ← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]

/-- The concrete period generator `2 * π * I` of the exponential at a complex
archimedean place, transported to the completion. -/
noncomputable def paperPeriod (hw : w.IsComplex) : w.Completion :=
  (completionRingEquivComplex D w hw).symm (2 * Real.pi * Complex.I)

/-- The period generator lies in the kernel of the exponential. -/
theorem archimedeanExp_paperPeriod (hw : w.IsComplex) :
    archimedeanExp D w (paperPeriod D w hw) = 1 := by
  rw [archimedeanExp_of_isComplex D w hw, paperPeriod, RingEquiv.apply_symm_apply,
    Complex.exp_two_pi_mul_I, map_one]

/-- The period generator is nonzero. -/
theorem paperPeriod_ne_zero (hw : w.IsComplex) : paperPeriod D w hw ≠ 0 := by
  intro h
  have hp : (completionRingEquivComplex D w hw) (paperPeriod D w hw)
      = 2 * Real.pi * Complex.I := by
    rw [paperPeriod, RingEquiv.apply_symm_apply]
  rw [h, map_zero] at hp
  have h2 : (2 * Real.pi : Complex) ≠ 0 := by
    refine mul_ne_zero (by norm_num) ?_
    rw [Complex.ofReal_ne_zero]
    exact Real.pi_ne_zero
  exact Complex.I_ne_zero ((mul_eq_zero.mp hp.symm).resolve_left h2)

/-- The norm of the period generator is `2 * π`. -/
theorem norm_paperPeriod (hw : w.IsComplex) : ‖paperPeriod D w hw‖ = 2 * Real.pi := by
  rw [paperPeriod, norm_completionRingEquivComplex_symm D w hw]
  rw [Complex.norm_mul, Complex.norm_mul]
  rw [Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  norm_num

/-- The kernel of the exponential at a complex place is exactly the period
lattice `2πi Z`, transported: the period generator generates it. -/
theorem archimedeanExp_eq_one_iff (hw : w.IsComplex) (z : w.Completion) :
    archimedeanExp D w z = 1 ↔ ∃ n : ℤ, z = n • paperPeriod D w hw := by
  constructor
  · intro h
    have h2 : Complex.exp ((completionRingEquivComplex D w hw) z) = 1 := by
      have hh := congrArg (completionRingEquivComplex D w hw)
        (archimedeanExp_of_isComplex D w hw z ▸ h)
      simpa using hh
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h2
    refine ⟨n, ?_⟩
    have hz : z = (completionRingEquivComplex D w hw).symm
        ((n : Complex) * (2 * (Real.pi : Complex) * Complex.I)) := by
      rw [← hn, RingEquiv.symm_apply_apply]
    rw [hz, paperPeriod]
    rw [show ((n : Complex) * (2 * (Real.pi : Complex) * Complex.I))
        = n • (2 * (Real.pi : Complex) * Complex.I) by rw [zsmul_eq_mul]]
    rw [map_zsmul]
  · rintro ⟨n, hz⟩
    rw [hz, archimedeanExp_of_isComplex D w hw]
    have hmap : (completionRingEquivComplex D w hw)
        (n • (completionRingEquivComplex D w hw).symm
          (2 * (Real.pi : Complex) * Complex.I))
        = (n : Complex) * (2 * (Real.pi : Complex) * Complex.I) := by
      rw [map_zsmul, RingEquiv.apply_symm_apply, zsmul_eq_mul]
    rw [paperPeriod, hmap, Complex.exp_int_mul_two_pi_mul_I, map_one]

/-! ## 2. The π-normalized log-shell -/

/-- The paper's archimedean log-shell `I_k = {a ∈ k | |a| ≤ π}`
([IUTchIII], Remark 1.2.2, (ii)). -/
def paperLogShell : Set w.Completion :=
  {x | ‖x‖ ≤ Real.pi}

/-- The log-shell is the closed unit ball of the `π`-normalized seminorm
`x ↦ ‖x‖ / π`. -/
theorem paperLogShell_eq_piSeminorm_ball :
    paperLogShell D w = {x : w.Completion | ‖x‖ / Real.pi ≤ 1} := by
  ext x
  simp only [paperLogShell, Set.mem_setOf_eq]
  rw [div_le_one Real.pi_pos]

/-- The log-shell contains `0`. -/
theorem zero_mem_paperLogShell : (0 : w.Completion) ∈ paperLogShell D w := by
  simp only [paperLogShell, Set.mem_setOf_eq, norm_zero]
  exact Real.pi_pos.le

/-- The actual closed unit ball `O_k` is contained in the log-shell — `(b^arc)`
of [IUTchIII], Proposition 1.2, (v), in the concrete model of
Remark 1.2.2, (ii). -/
theorem archimedeanUnitBall_subset_paperLogShell :
    archimedeanUnitBall D w ⊆ paperLogShell D w := by
  intro x hx
  simp only [archimedeanUnitBall, Set.mem_setOf_eq] at hx
  simp only [paperLogShell, Set.mem_setOf_eq]
  have h1 : (1 : Real) ≤ Real.pi := by linarith [Real.pi_gt_three]
  linarith

/-- The log-shell is compact. -/
theorem isCompact_paperLogShell : IsCompact (paperLogShell D w) := by
  by_cases hw : w.IsComplex
  · have hp : paperLogShell D w =
        (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw) ⁻¹'
          Metric.closedBall (0 : Complex) Real.pi := by
      ext x
      simp only [paperLogShell, Set.mem_setOf_eq, Set.mem_preimage, Metric.mem_closedBall,
        dist_zero_right]
      change ‖x‖ ≤ Real.pi ↔
        ‖(NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw) x‖
          ≤ Real.pi
      rw [show (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw) x
          = (completionRingEquivComplex D w hw) x from rfl,
        ringEquivComplexOfIsComplex_norm D w hw x]
    rw [hp]
    exact
      (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).toHomeomorph.isCompact_preimage.mpr
        (isCompact_closedBall (0 : Complex) Real.pi)
  · have hreal : w.IsReal := NumberField.InfinitePlace.not_isComplex_iff_isReal.mp hw
    have hp : paperLogShell D w =
        (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hreal) ⁻¹'
          Metric.closedBall (0 : Real) Real.pi := by
      ext x
      simp only [paperLogShell, Set.mem_setOf_eq, Set.mem_preimage, Metric.mem_closedBall,
        dist_zero_right]
      change ‖x‖ ≤ Real.pi ↔
        ‖(NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hreal) x‖
          ≤ Real.pi
      rw [show (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hreal) x
          = (completionRingEquivReal D w hreal) x from rfl,
        ringEquivRealOfIsReal_norm D w hreal x]
    rw [hp]
    exact
      (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hreal).toHomeomorph.isCompact_preimage.mpr
        (isCompact_closedBall (0 : Real) Real.pi)

/-- The units are contained in the log-shell. -/
theorem archimedeanUnitSphere_subset_paperLogShell :
    archimedeanUnitSphere D w ⊆ paperLogShell D w := by
  intro u hu
  simp only [archimedeanUnitSphere, Set.mem_setOf_eq] at hu
  simp only [paperLogShell, Set.mem_setOf_eq]
  have h1 : (1 : Real) ≤ Real.pi := by linarith [Real.pi_gt_three]
  rw [hu]
  exact h1

/-- `(c^arc)` of [IUTchIII], Proposition 1.2, (v), in the concrete model: every
unit is the exponential of a point of the log-shell. -/
theorem exists_logShell_exp_of_unit {u : w.Completion} (hw : w.IsComplex)
    (hu : u ∈ archimedeanUnitSphere D w) :
    ∃ x : w.Completion, x ∈ paperLogShell D w ∧ archimedeanExp D w x = u := by
  have hu1 : ‖u‖ = 1 := hu
  set e := completionRingEquivComplex D w hw with he
  set y : Complex := e u with hy
  have hy1 : ‖y‖ = 1 := by
    rw [hy, ringEquivComplexOfIsComplex_norm D w hw u]
    exact hu1
  have hy0 : y ≠ 0 := by
    rintro h0
    rw [h0] at hy1
    simp at hy1
  set θ : Real := y.arg with hθ
  have hθpi : |θ| ≤ Real.pi := Complex.abs_arg_le_pi y
  have hey : Complex.exp ((θ : Complex) * Complex.I) = y := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    have hcos : Real.cos θ = y.re := by
      rw [hθ, Complex.cos_arg hy0, hy1, div_one]
    have hsin : Real.sin θ = y.im := by
      rw [hθ, Complex.sin_arg, hy1, div_one]
    rw [hcos, hsin]
    exact Complex.re_add_im y
  refine ⟨e.symm ((θ : Complex) * Complex.I), ?_, ?_⟩
  · simp only [paperLogShell, Set.mem_setOf_eq]
    rw [norm_completionRingEquivComplex_symm D w hw]
    rw [Complex.norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact hθpi
  · rw [archimedeanExp_of_isComplex D w hw, he, RingEquiv.apply_symm_apply, hey]
    exact RingEquiv.symm_apply_apply e u

/-- `(c^arc)`: the compact unit group is contained in the exponential image of
the log-shell (a surjectivity statement, not an equality). -/
theorem archimedeanUnitSphere_subset_exp_paperLogShell (hw : w.IsComplex) :
    archimedeanUnitSphere D w ⊆ archimedeanExp D w '' paperLogShell D w := by
  intro u hu
  exact exists_logShell_exp_of_unit D w hw hu

/-- The reverse containment fails: the exponential does not map the log-shell
into itself, so the log-link diagram is genuinely non-commutative
(cf. [IUTchIII], Remark 1.2.2, (iii), (iv): only upper semi-commutativity
holds). -/
theorem not_exp_paperLogShell_subset (hw : w.IsComplex) :
    ¬ (archimedeanExp D w '' paperLogShell D w ⊆ paperLogShell D w) := by
  intro h
  have hmem : (completionRingEquivComplex D w hw).symm (Real.pi : Complex)
      ∈ paperLogShell D w := by
    simp only [paperLogShell, Set.mem_setOf_eq]
    rw [norm_completionRingEquivComplex_symm D w hw, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  have himg := h ⟨_, hmem, rfl⟩
  simp only [paperLogShell, Set.mem_setOf_eq] at himg
  rw [archimedeanExp_of_isComplex D w hw, RingEquiv.apply_symm_apply,
    norm_completionRingEquivComplex_symm D w hw, Complex.norm_exp, Complex.ofReal_re] at himg
  have hlt : Real.pi < Real.exp Real.pi := by
    have h' := Real.add_one_le_exp Real.pi
    linarith [Real.pi_gt_three]
  linarith

/-- The log-shell strictly contains the plain unit ball: the point `π` lies in
the log-shell but not in the closed unit ball. -/
theorem exists_paperLogShell_not_unitBall (hw : w.IsComplex) :
    ∃ x : w.Completion, x ∈ paperLogShell D w ∧ x ∉ archimedeanUnitBall D w := by
  refine ⟨(completionRingEquivComplex D w hw).symm (Real.pi : Complex), ?_, ?_⟩
  · simp only [paperLogShell, Set.mem_setOf_eq]
    rw [norm_completionRingEquivComplex_symm D w hw, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  · simp only [archimedeanUnitBall, Set.mem_setOf_eq]
    rw [norm_completionRingEquivComplex_symm D w hw, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    have h1 : (1 : Real) < Real.pi := by linarith [Real.pi_gt_three]
    linarith
/-! ## 3. The fundamental closed segment and its unit orbit -/

/-- The fundamental closed line segment at a complex place: the closed segment
`[-πi, πi] ⊆ C`, transported to the completion.  It is preserved by
multiplication by `±1`, and its endpoints differ by the period generator. -/
noncomputable def paperFundamentalSegment (hw : w.IsComplex) : Set w.Completion :=
  (completionRingEquivComplex D w hw).symm ''
    segment ℝ (-((Real.pi : Complex) * Complex.I)) ((Real.pi : Complex) * Complex.I)

/-- Concrete parametrisation of the fundamental segment in `C` by the imaginary
coordinate `r ∈ [-π, π]`. -/
theorem mem_segment_complex_iff (y : Complex) :
    y ∈ segment ℝ (-((Real.pi : Complex) * Complex.I)) ((Real.pi : Complex) * Complex.I) ↔
      ∃ r : Real, r ∈ Set.Icc (-Real.pi) Real.pi ∧ y = (r : Complex) * Complex.I := by
  rw [segment_eq_image]
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    refine ⟨(2 * θ - 1) * Real.pi, ⟨?_, ?_⟩, ?_⟩
    · nlinarith [hθ.1, Real.pi_pos]
    · nlinarith [hθ.2, Real.pi_pos]
    · dsimp only
      rw [Complex.real_smul, Complex.real_smul]
      push_cast
      ring
  · rintro ⟨r, hr, rfl⟩
    refine ⟨(r / Real.pi + 1) / 2, ⟨?_, ?_⟩, ?_⟩
    · have h1 : (-1 : Real) ≤ r / Real.pi := by
        rw [le_div_iff₀ Real.pi_pos]
        linarith [hr.1]
      linarith
    · have h1 : r / Real.pi ≤ 1 := by
        rw [div_le_one Real.pi_pos]
        exact hr.2
      linarith
    · dsimp only
      rw [Complex.real_smul, Complex.real_smul]
      push_cast
      field_simp
      ring

/-- Points of the fundamental segment, parametrised in the completion. -/
theorem mem_paperFundamentalSegment_iff (hw : w.IsComplex) (x : w.Completion) :
    x ∈ paperFundamentalSegment D w hw ↔
      ∃ r : Real, r ∈ Set.Icc (-Real.pi) Real.pi ∧
        x = (completionRingEquivComplex D w hw).symm ((r : Complex) * Complex.I) := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨r, hr, rfl⟩ := (mem_segment_complex_iff y).mp hy
    exact ⟨r, hr, rfl⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨_, (mem_segment_complex_iff _).mpr ⟨r, hr, rfl⟩, rfl⟩

/-- Every point of the fundamental segment lies in the log-shell. -/
theorem paperFundamentalSegment_norm_le (hw : w.IsComplex) {x : w.Completion}
    (hx : x ∈ paperFundamentalSegment D w hw) : ‖x‖ ≤ Real.pi := by
  obtain ⟨r, hr, rfl⟩ := (mem_paperFundamentalSegment_iff D w hw x).mp hx
  rw [norm_completionRingEquivComplex_symm D w hw, Complex.norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs]
  exact abs_le.mpr hr

/-- The fundamental segment is contained in the log-shell. -/
theorem paperFundamentalSegment_subset_paperLogShell (hw : w.IsComplex) :
    paperFundamentalSegment D w hw ⊆ paperLogShell D w :=
  fun _ hx => paperFundamentalSegment_norm_le D w hw hx

/-- The endpoints of the fundamental segment differ by the period generator. -/
theorem paperFundamentalSegment_endpoint_sub (hw : w.IsComplex) :
    (completionRingEquivComplex D w hw).symm ((Real.pi : Complex) * Complex.I) -
      (completionRingEquivComplex D w hw).symm (-((Real.pi : Complex) * Complex.I))
      = paperPeriod D w hw := by
  rw [← map_sub, paperPeriod]
  congr 1
  ring

/-- The fundamental segment is preserved by multiplication by `±1`. -/
theorem neg_mem_paperFundamentalSegment (hw : w.IsComplex) {x : w.Completion}
    (hx : x ∈ paperFundamentalSegment D w hw) : -x ∈ paperFundamentalSegment D w hw := by
  obtain ⟨r, hr, rfl⟩ := (mem_paperFundamentalSegment_iff D w hw x).mp hx
  rw [mem_paperFundamentalSegment_iff]
  refine ⟨-r, ⟨by linarith [hr.2], by linarith [hr.1]⟩, ?_⟩
  rw [← map_neg]
  congr 1
  rw [Complex.ofReal_neg]
  ring

/-- **The orbit identity of [IUTchIII], Definition 1.1, (ii), in the concrete
model**: the log-shell is exactly the orbit of the fundamental segment under the
compact unit group `O_k^×` of the archimedean local field. -/
theorem mem_paperLogShell_iff_unit_mul_segment (hw : w.IsComplex) (x : w.Completion) :
    x ∈ paperLogShell D w ↔
      ∃ u s : w.Completion,
        ‖u‖ = 1 ∧ s ∈ paperFundamentalSegment D w hw ∧ x = u * s := by
  constructor
  · intro hx
    have hxpi : ‖x‖ ≤ Real.pi := hx
    by_cases hx0 : x = 0
    · refine ⟨1, 0, by simp, ?_, by simp [hx0]⟩
      rw [mem_paperFundamentalSegment_iff]
      exact ⟨0, ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩, by simp⟩
    · have hxpos : 0 < ‖x‖ :=
        lt_of_le_of_ne (norm_nonneg x) (Ne.symm (norm_ne_zero_iff.mpr hx0))
      refine ⟨x * ((completionRingEquivComplex D w hw).symm ((‖x‖ : Complex) * Complex.I))⁻¹,
        (completionRingEquivComplex D w hw).symm ((‖x‖ : Complex) * Complex.I), ?_, ?_, ?_⟩
      · rw [norm_mul, norm_inv, norm_completionRingEquivComplex_symm D w hw, Complex.norm_mul,
          Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (norm_nonneg x), mul_inv_cancel₀ hxpos.ne']
      · rw [mem_paperFundamentalSegment_iff]
        exact ⟨‖x‖, ⟨by linarith [norm_nonneg x], hxpi⟩, rfl⟩
      · rw [mul_assoc, inv_mul_cancel₀, mul_one]
        intro h0
        have hnorm : ‖(completionRingEquivComplex D w hw).symm
            ((‖x‖ : Complex) * Complex.I)‖ = 0 := by rw [h0, norm_zero]
        rw [norm_completionRingEquivComplex_symm D w hw, Complex.norm_mul, Complex.norm_I,
          mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (norm_nonneg x)] at hnorm
        exact hxpos.ne' hnorm
  · rintro ⟨u, s, hu, hs, rfl⟩
    simp only [paperLogShell, Set.mem_setOf_eq]
    rw [norm_mul, hu, one_mul]
    exact paperFundamentalSegment_norm_le D w hw hs

/-- The log-shell is invariant under the compact unit group `O_k^×`. -/
theorem smul_unit_mem_paperLogShell (_hw : w.IsComplex) {u : w.Completion}
    (hu : ‖u‖ = 1) {x : w.Completion} (hx : x ∈ paperLogShell D w) :
    u * x ∈ paperLogShell D w := by
  simp only [paperLogShell, Set.mem_setOf_eq] at hx ⊢
  rw [norm_mul, hu, one_mul]
  exact hx

/-! ## 4. The full paper archimedean log-shell datum -/

/-- The full, period-carrying archimedean log-shell datum at an infinite place
`w` of `Fmod`: the shape of [IUTchIII], Definition 1.1, (ii), together with the
archimedean properties `(b^arc)`, `(c^arc)` of Proposition 1.2, (v) and the
"upper semi-commutativity" of Remark 1.2.2, (iii).

Compared with the reduced S1927 `ArchimedeanLogShellDatum`, the containment
`logShell ⊆ O_k` is **replaced** by its opposite `O_k ⊆ logShell` (the paper's
`(b^arc)`), and the following data are added:

* the period generator `period`, with `exp period = 1` and the kernel
  characterisation `ker exp = period • Z`;
* the fundamental closed line segment, preserved by multiplication by `±1`,
  whose endpoints differ by the period;
* the orbit identity `logShell = O_k^× · (fundamental segment)`;
* the log-link upper semi-commutativity `O_k^× ⊆ exp '' logShell`. -/
structure PaperArchimedeanLogShellDatum
    (D : S1895PaperInput) (w : NumberField.InfinitePlace (PaperFmod D)) where
  [moduleK : Module Real w.Completion]
  /-- the archimedean log-shell `I_k` -/
  logShell : Set w.Completion
  /-- `(a^arc)`: the log-shell is compact -/
  isCompact_logShell : IsCompact logShell
  /-- the closed disk/interval shape is convex over `R` -/
  convex_logShell : Convex Real logShell
  /-- the log-shell contains `0` -/
  zero_mem_logShell : (0 : w.Completion) ∈ logShell
  /-- `(b^arc)`: the actual closed unit ball is contained in the log-shell -/
  unitBall_subset_logShell : archimedeanUnitBall D w ⊆ logShell
  /-- the period generator of the exponential (=`2πi` at a complex place) -/
  period : w.Completion
  period_ne_zero : period ≠ 0
  /-- the period generator lies in the kernel of the exponential -/
  exp_period : archimedeanExp D w period = 1
  /-- the period generator generates the kernel of the exponential -/
  period_generates_kernel : ∀ z : w.Completion,
    archimedeanExp D w z = 1 ↔ ∃ n : ℤ, z = n • period
  /-- the fundamental closed line segment -/
  fundamentalSegment : Set w.Completion
  /-- it is a closed line segment preserved by `±1`, with endpoint difference
  equal to the period -/
  fundamentalSegment_isSegment : ∃ a b : w.Completion,
    fundamentalSegment = segment Real a b ∧ b - a = period ∧ b = -a
  /-- the endpoints of the fundamental segment are points of it: the usable form
  of `fundamentalSegment_isSegment` for the closed segment `[-πi, πi]` -/
  fundamentalSegment_endpoints_mem : ∃ a b : w.Completion,
    a ∈ fundamentalSegment ∧ b ∈ fundamentalSegment ∧ b - a = period ∧ b = -a
  fundamentalSegment_subset_logShell : fundamentalSegment ⊆ logShell
  /-- the log-shell is the orbit of the fundamental segment under the compact
  unit group `O_k^×` ([IUTchIII], Definition 1.1, (ii)) -/
  logShell_eq_unitOrbit : ∀ x : w.Completion,
    x ∈ logShell ↔
      ∃ u s : w.Completion, ‖u‖ = 1 ∧ s ∈ fundamentalSegment ∧ x = u * s
  /-- `(c^arc)` / log-link upper semi-commutativity: the compact unit group is
  contained in the exponential image of the log-shell (a surjectivity statement,
  not an equality) -/
  units_subset_exp_logShell :
    archimedeanUnitSphere D w ⊆ archimedeanExp D w '' logShell

namespace PaperArchimedeanLogShellDatum

variable {D : S1895PaperInput} {w : NumberField.InfinitePlace (PaperFmod D)}

/-- The log-link upper semi-commutativity data of the full datum, packaged:
the unit ball is contained in the log-shell and the compact unit group is
contained in the exponential image of the log-shell.  Both inclusions are
one-sided, in accordance with [IUTchIII], Remark 1.2.2, (iii), (iv). -/
theorem logLink_upperSemi (F : PaperArchimedeanLogShellDatum D w) :
    archimedeanUnitBall D w ⊆ F.logShell ∧
      archimedeanUnitSphere D w ⊆ archimedeanExp D w '' F.logShell :=
  ⟨F.unitBall_subset_logShell, F.units_subset_exp_logShell⟩

/-- The period is a difference of two points of the log-shell. -/
theorem exists_sub_eq_period (F : PaperArchimedeanLogShellDatum D w) :
    ∃ a b : w.Completion, a ∈ F.logShell ∧ b ∈ F.logShell ∧ b - a = F.period := by
  obtain ⟨a, b, ha, hb, hsub, _⟩ := F.fundamentalSegment_endpoints_mem
  exact ⟨a, b, F.fundamentalSegment_subset_logShell ha,
    F.fundamentalSegment_subset_logShell hb, hsub⟩

end PaperArchimedeanLogShellDatum

/-! ## 5. The construction at a complex archimedean place -/

/-- The full paper archimedean log-shell datum at a complex place: the
`π`-disk `I_k = {‖x‖ ≤ π}` together with the period generator `2πi`, the
fundamental segment `[-πi, πi]`, its `O_k^×`-orbit identity and the log-link
upper semi-commutativity.  All fields are proved from the actual metric data of
`w.Completion`. -/
noncomputable def paperArchimedeanLogShellDatum (hw : w.IsComplex) :
    PaperArchimedeanLogShellDatum D w := by
  classical
  letI : Module Real w.Completion := archimedeanModuleOfIsComplex D w hw
  let e := completionRingEquivComplex D w hw
  have hsmul : ∀ (r : Real) (y : Complex), e.symm (r • y) = r • e.symm y := by
    intro r y
    change e.symm (r • y) = e.symm (algebraMap Real Complex r) * e.symm y
    rw [← map_mul]
    congr 1
  have himage : ∀ a₀ b₀ : Complex,
      e.symm '' (segment Real a₀ b₀) = segment Real (e.symm a₀) (e.symm b₀) := by
    intro a₀ b₀
    rw [segment_eq_image, segment_eq_image, Set.image_image]
    congr 1
    funext θ
    rw [map_add, hsmul, hsmul]
  refine
    { moduleK := archimedeanModuleOfIsComplex D w hw
      logShell := paperLogShell D w
      isCompact_logShell := isCompact_paperLogShell D w
      convex_logShell := ?_
      zero_mem_logShell := zero_mem_paperLogShell D w
      unitBall_subset_logShell := archimedeanUnitBall_subset_paperLogShell D w
      period := paperPeriod D w hw
      period_ne_zero := paperPeriod_ne_zero D w hw
      exp_period := archimedeanExp_paperPeriod D w hw
      period_generates_kernel := archimedeanExp_eq_one_iff D w hw
      fundamentalSegment := paperFundamentalSegment D w hw
      fundamentalSegment_isSegment := ?_
      fundamentalSegment_endpoints_mem := ?_
      fundamentalSegment_subset_logShell := paperFundamentalSegment_subset_paperLogShell D w hw
      logShell_eq_unitOrbit := mem_paperLogShell_iff_unit_mul_segment D w hw
      units_subset_exp_logShell := archimedeanUnitSphere_subset_exp_paperLogShell D w hw }
  · -- the π-disk is convex
    let L : w.Completion →ₗ[Real] Complex :=
      { toFun := fun x => e x
        map_add' := fun x y => map_add e x y
        map_smul' := by
          intro r x
          change e (e.symm (algebraMap Real Complex r) * x) = algebraMap Real Complex r * e x
          rw [map_mul, RingEquiv.apply_symm_apply] }
    have hball : paperLogShell D w = L ⁻¹' Metric.closedBall (0 : Complex) Real.pi := by
      ext x
      simp only [paperLogShell, Set.mem_setOf_eq, Set.mem_preimage, Metric.mem_closedBall,
        dist_zero_right]
      change ‖x‖ ≤ Real.pi ↔ ‖L x‖ ≤ Real.pi
      rw [show L x = e x from rfl, ringEquivComplexOfIsComplex_norm D w hw x]
    rw [hball]
    exact (convex_closedBall (0 : Complex) Real.pi).linear_preimage L
  · -- the fundamental segment is the closed segment [-πi, πi]
    refine ⟨e.symm (-((Real.pi : Complex) * Complex.I)),
      e.symm ((Real.pi : Complex) * Complex.I), ?_, ?_, ?_⟩
    · rw [paperFundamentalSegment, himage]
    · exact paperFundamentalSegment_endpoint_sub D w hw
    · rw [map_neg]
      ring
  · -- the endpoints of the segment are points of the segment
    refine ⟨e.symm (-((Real.pi : Complex) * Complex.I)),
      e.symm ((Real.pi : Complex) * Complex.I), ?_, ?_, ?_, ?_⟩
    · rw [mem_paperFundamentalSegment_iff]
      refine ⟨-Real.pi, ⟨le_rfl, by linarith [Real.pi_pos]⟩, ?_⟩
      congr 1
      rw [Complex.ofReal_neg]
      ring
    · rw [mem_paperFundamentalSegment_iff]
      exact ⟨Real.pi, ⟨by linarith [Real.pi_pos], le_rfl⟩, rfl⟩
    · exact paperFundamentalSegment_endpoint_sub D w hw
    · rw [map_neg]
      ring

/-- The log-shell of the constructed datum is the paper's `π`-disk. -/
@[simp] theorem paperArchimedeanLogShellDatum_logShell (hw : w.IsComplex) :
    (paperArchimedeanLogShellDatum D w hw).logShell = paperLogShell D w := rfl

/-- The period generator of the constructed datum is `2πi`. -/
@[simp] theorem paperArchimedeanLogShellDatum_period (hw : w.IsComplex) :
    (paperArchimedeanLogShellDatum D w hw).period = paperPeriod D w hw := rfl

/-- The fundamental segment of the constructed datum is `[-πi, πi]`. -/
@[simp] theorem paperArchimedeanLogShellDatum_segment (hw : w.IsComplex) :
    (paperArchimedeanLogShellDatum D w hw).fundamentalSegment =
      paperFundamentalSegment D w hw := rfl

/-- The full paper archimedean log-shell datum is inhabited at every complex
archimedean place. -/
theorem nonempty_paperArchimedeanLogShellDatum (hw : w.IsComplex) :
    Nonempty (PaperArchimedeanLogShellDatum D w) :=
  ⟨paperArchimedeanLogShellDatum D w hw⟩
/-! ## 6. The exact first missing: normalization and the real-place boundary -/

/-- Any full paper datum at a complex place has period of norm at least `2π`:
the period is a nonzero element of the lattice `2πi Z`. -/
theorem two_pi_le_norm_period (hw : w.IsComplex)
    (F : PaperArchimedeanLogShellDatum D w) :
    2 * Real.pi ≤ ‖F.period‖ := by
  obtain ⟨n, hn⟩ := (archimedeanExp_eq_one_iff D w hw F.period).mp F.exp_period
  have hn0 : n ≠ 0 := by
    intro h0
    rw [h0] at hn
    simp only [zero_zsmul] at hn
    exact F.period_ne_zero hn
  rw [hn, zsmul_eq_mul, norm_mul, norm_intCast_completion D w hw,
    norm_paperPeriod D w hw]
  have h1 : (1 : Real) ≤ |(n : Real)| := by
    have h2 : (1 : Int) ≤ |n| := Int.one_le_abs hn0
    have h3 : ((1 : Int) : Real) ≤ ((|n| : Int) : Real) := by exact_mod_cast h2
    rwa [Int.cast_abs, Int.cast_one] at h3
  nlinarith [Real.pi_pos, h1]

/-- **The reduced S1927 normalization is incompatible with the full paper
datum.**  No full paper datum at a complex place can have its log-shell
contained in the actual closed unit ball: the period is a difference of two
points of the log-shell, whence `‖period‖ ≤ 2`, while the actual period has
`‖period‖ ≥ 2π > 2`. -/
theorem no_logShell_subset_unitBall (hw : w.IsComplex)
    (F : PaperArchimedeanLogShellDatum D w) :
    ¬ F.logShell ⊆ archimedeanUnitBall D w := by
  intro hsub
  obtain ⟨a, b, ha, hb, hsub', _⟩ := F.fundamentalSegment_endpoints_mem
  have ha1 : ‖a‖ ≤ 1 := hsub (F.fundamentalSegment_subset_logShell ha)
  have hb1 : ‖b‖ ≤ 1 := hsub (F.fundamentalSegment_subset_logShell hb)
  have h3 : ‖F.period‖ ≤ 2 := by
    calc ‖F.period‖ = ‖b - a‖ := by rw [hsub']
      _ ≤ ‖b‖ + ‖a‖ := norm_sub_le b a
      _ ≤ 2 := by linarith
  have h4 := two_pi_le_norm_period D w hw F
  have hpi : (2 : Real) < 2 * Real.pi := by linarith [Real.pi_gt_three]
  linarith

/-- **The full paper datum does not exist at a real archimedean place**: the
period group of the real exponential is trivial, so the required nonzero period
generator cannot exist.  (This is consistent with [IUTchI], Definition 3.1, (a),
`√-1 ∈ F`, and [IUTchIII], Remark 1.2.2, (ii): archimedean places in an initial
Θ-datum are complex archimedean fields.) -/
theorem real_place_not_inhabited (hreal : w.IsReal) :
    ¬ Nonempty (PaperArchimedeanLogShellDatum D w) := by
  rintro ⟨F⟩
  have h := F.exp_period
  rw [archimedeanExp_of_isReal D w hreal] at h
  have h2 : (completionRingEquivReal D w hreal) F.period = 0 := by
    have hh : Real.exp ((completionRingEquivReal D w hreal) F.period) = 1 := by
      have hh' := congrArg (completionRingEquivReal D w hreal) h
      simpa using hh'
    exact (Real.exp_eq_one_iff _).mp hh
  have h3 : F.period = 0 := by
    rw [← RingEquiv.symm_apply_apply (completionRingEquivReal D w hreal) F.period, h2,
      map_zero]
  exact F.period_ne_zero h3

/-- S1950's reduced datum — whose log-shell is the whole actual closed unit ball —
cannot be upgraded to a full paper datum. -/
theorem s1950_not_full (hw : w.IsComplex) :
    ¬ ∃ F : PaperArchimedeanLogShellDatum D w,
        F.logShell = (paperArchimedeanLogShell D w).logShell := by
  rintro ⟨F, hF⟩
  refine no_logShell_subset_unitBall D w hw F ?_
  rw [hF, paperArchimedeanLogShell_logShell]

/-- The constructed datum's log-shell is not contained in the plain unit ball. -/
theorem constructed_logShell_not_subset_unitBall (hw : w.IsComplex) :
    ¬ (paperArchimedeanLogShellDatum D w hw).logShell ⊆ archimedeanUnitBall D w :=
  no_logShell_subset_unitBall D w hw (paperArchimedeanLogShellDatum D w hw)

/-- The plain unit ball is strictly contained in the paper's log-shell. -/
theorem archimedeanUnitBall_ssubset_paperLogShell (hw : w.IsComplex) :
    archimedeanUnitBall D w ⊂ paperLogShell D w := by
  refine ⟨archimedeanUnitBall_subset_paperLogShell D w, ?_⟩
  intro hcontra
  obtain ⟨x, hx, hx'⟩ := exists_paperLogShell_not_unitBall D w hw
  exact hx' (hcontra hx)

/-- **The exact boundary of S1954.**  At a complex archimedean place the full,
period-carrying archimedean log-shell datum exists; at a real place it provably
does not; and at a complex place *every* full datum has its log-shell strictly
larger than — hence not contained in — the reduced S1927 closed unit ball.  Thus
S1950's reduced datum is not a normalization of the paper's datum: the passage
from the plain completion norm to the `π`-normalized one is exactly what the
period generator `2πi` forces. -/
theorem s1954_exact_boundary :
    (∀ (hw : w.IsComplex), Nonempty (PaperArchimedeanLogShellDatum D w)) ∧
      (∀ (hreal : w.IsReal), ¬ Nonempty (PaperArchimedeanLogShellDatum D w)) ∧
        (∀ (hw : w.IsComplex) (F : PaperArchimedeanLogShellDatum D w),
          ¬ F.logShell ⊆ archimedeanUnitBall D w) :=
  ⟨fun hw => nonempty_paperArchimedeanLogShellDatum D w hw,
    fun hreal => real_place_not_inhabited D w hreal,
    fun hw F => no_logShell_subset_unitBall D w hw F⟩

/-- The full paper datum carries the period `2πi`, whose norm is the length
`2π` of `O_k^× ⊆ k` ([IUTchIII], Remark 3.9.4, (vi)). -/
theorem constructed_period_norm_and_endpoints (hw : w.IsComplex) :
    (paperArchimedeanLogShellDatum D w hw).period = paperPeriod D w hw ∧
      ‖(paperArchimedeanLogShellDatum D w hw).period‖ = 2 * Real.pi :=
  ⟨rfl, norm_paperPeriod D w hw⟩

/-! ## 7. Axiom probes -/

#print axioms archimedeanExp_eq_one_iff
#print axioms mem_paperLogShell_iff_unit_mul_segment
#print axioms paperArchimedeanLogShellDatum
#print axioms no_logShell_subset_unitBall
#print axioms real_place_not_inhabited
#print axioms s1950_not_full
#print axioms s1954_exact_boundary

end LeanFormal.IUT.XiFPaper.S1954ArchimedeanPeriodActual
