import tmp.sheaf.xif.paper.S1927GlobalFrobenioidLogShellActual
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# S1950: the actual archimedean log-shell at every infinite place

## What is constructed

S1927 records its exact first missing object as

  S1927FirstMissing D = (w : InfinitePlace (PaperFmod D)) ->
    ArchimedeanLogShellDatum D w

where `w.Completion` is Mathlib's actual completion of the number field at the
infinite place `w` (a complete normed field canonically isomorphic to `R` or
`C`), and `ArchimedeanLogShellDatum D w` records a compact convex set of
`w.Completion` which is contained in the actual closed unit ball
`{x | ‖x‖ ≤ 1}` and contains `0`.

This file constructs an inhabitant of `S1927FirstMissing D` for every S1895
paper input `D`.  At every `w`:

* the completion is isometric to `R` when `w.IsReal` and to `C` when
  `w.IsComplex`, via
  `NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal` and
  `NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex`;
  the underlying canonical ring equivalence
  (`ringEquivRealOfIsReal` / `ringEquivComplexOfIsComplex`) transports the
  canonical real vector space structure of `R` / `C` to `w.Completion` by
  `Module.compHom`;
* the log-shell is the **actual closed unit ball** `archimedeanUnitBall D w`.
  It is compact because it is the preimage of the compact closed unit ball of
  `R` / `C` under the isometry homeomorphism; it is convex because it is
  the preimage of a convex set under the induced real-linear isometry; it
  contains `0` and is contained in itself;
* the set is not degenerate: it is the whole closed unit ball and contains
  both `0` and `1`, so it is not the singleton `{0}`.

No `sorry`, `admit`, `axiom`, fake inhabitant, or empty-carrier device is
used.  The only classical input is the case distinction
`w.IsComplex` versus `w.IsReal` (which is a proposition, not a decidable
type), resolved by `Classical.choice`; the resulting proof dependencies are
exactly `propext`, `Classical.choice` and `Quot.sound`.

## The remaining exact first missing

Since the archimedean datum is constructed, the `archimedeanLogShell` field of
`S1927FullLogKummerUQ` is no longer an obstruction.  The exact remaining
missing input of the full log-Kummer package is the Kummer evaluation square
`S1927KummerEvaluationSquareActual D` (the actual four coric vertices
env/gau/LGP/lgp and the Kummer evaluation square on them).  This is recorded
precisely by

  Nonempty (S1927FullLogKummerUQ D) <->
    Nonempty (S1927KummerEvaluationSquareActual D).

## Honesty note

`ArchimedeanLogShellDatum` is explicitly the *reduced shape* of IUT III,
Definition 1.1, (ii): it only records compact convexity inside the closed unit
ball and membership of `0`.  The period generator `2*pi*i`, the closed
line-segment orbit under the local units, and the upper semi-commutativity
with the log-link are not part of this structure and are not claimed here.
What is constructed is the maximal (hence canonical) set allowed by the
reduced shape, namely the whole actual closed unit ball.  In the source
normalization in which the fundamental segment has endpoint difference
`2*pi*i`, the archimedean log-shell is the closed disk of radius `pi`, i.e.
the unit ball of the `pi`-normalized seminorm; the S1927 reduced datum uses
the plain completion norm, so the set constructed here is the correspondingly
normalized log-shell.
-/

noncomputable section
set_option maxHeartbeats 1600000

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.XiFPaper.S1927GlobalFrobenioidLogShellActual
open NumberField

namespace LeanFormal.IUT.XiFPaper.S1950ArchimedeanLogShellActual

variable (D : S1895PaperInput) (w : NumberField.InfinitePlace (PaperFmod D))

/-- The actual closed unit ball of the completion is Mathlib's metric closed
ball of radius one. -/
theorem archimedeanUnitBall_eq_closedBall :
    archimedeanUnitBall D w = Metric.closedBall (0 : w.Completion) 1 := by
  ext x
  simp [archimedeanUnitBall, Metric.mem_closedBall, dist_zero_right]

/-- The real vector space structure on the actual completion at a complex
place, transported from `C` along the canonical ring isomorphism
`w.Completion ≃+* C`.  The scalar action is the actual field multiplication
by the image of the real scalar; in particular `w.Completion` is an actual
real vector space, not an unrelated additive structure. -/
@[reducible] def archimedeanModuleOfIsComplex (hw : w.IsComplex) :
    Module Real w.Completion :=
  Module.compHom (M := w.Completion)
    ((NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm.toRingHom.comp
      (algebraMap Real Complex))

/-- The real vector space structure on the actual completion at a real place,
transported from `R` along the canonical ring isomorphism
`w.Completion ≃+* R`. -/
@[reducible] def archimedeanModuleOfIsReal (hreal : w.IsReal) :
    Module Real w.Completion :=
  Module.compHom (M := w.Completion)
    (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hreal).symm.toRingHom

/-- The canonical ring isomorphism at a complex place preserves norms (it is
an isometry). -/
theorem ringEquivComplexOfIsComplex_norm (hw : w.IsComplex) (x : w.Completion) :
    ‖NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw x‖ = ‖x‖ := by
  have h0 :
      (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).toFun 0 = 0 := by
    change NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw 0 = 0
    exact map_zero _
  have h :=
    (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).isometry_toFun.dist_eq
      x 0
  rw [dist_eq_norm, dist_eq_norm, h0, sub_zero, sub_zero] at h
  change ‖NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw x‖ = ‖x‖ at h
  exact h

/-- The canonical ring isomorphism at a real place preserves norms (it is an
isometry). -/
theorem ringEquivRealOfIsReal_norm (hreal : w.IsReal) (x : w.Completion) :
    ‖NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hreal x‖ = ‖x‖ := by
  have h0 :
      (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hreal).toFun 0 = 0 := by
    change NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hreal 0 = 0
    exact map_zero _
  have h :=
    (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hreal).isometry_toFun.dist_eq
      x 0
  rw [dist_eq_norm, dist_eq_norm, h0, sub_zero, sub_zero] at h
  change ‖NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hreal x‖ = ‖x‖ at h
  exact h

/-- The actual archimedean log-shell datum at an infinite place `w` of
`Fmod`: the maximal compact convex subset of the actual closed unit ball,
namely the whole actual closed unit ball.  The substrate is the actual
completion `w.Completion`, with the real vector space structure transported
from the canonical isometric identification with `R` or `C`; the compactness
and convexity proofs are the actual metric and vector-space facts, not
placeholder fields. -/
noncomputable def paperArchimedeanLogShellDatum :
    ArchimedeanLogShellDatum D w := by
  classical
  by_cases hw : w.IsComplex
  · letI : Module Real w.Completion := archimedeanModuleOfIsComplex D w hw
    let e := NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
    let L : w.Completion →ₗ[Real] Complex :=
      { toFun := fun x => e x
        map_add' := fun x y => map_add e x y
        map_smul' := by
          intro r x
          change e (e.symm (algebraMap Real Complex r) * x) =
            algebraMap Real Complex r * e x
          rw [map_mul, RingEquiv.apply_symm_apply] }
    have hballConv : archimedeanUnitBall D w = L ⁻¹' Metric.closedBall (0 : Complex) 1 := by
      ext x
      simp only [archimedeanUnitBall, Set.mem_setOf_eq, Set.mem_preimage, Metric.mem_closedBall,
        dist_zero_right]
      change ‖x‖ ≤ 1 ↔ ‖L x‖ ≤ 1
      rw [show L x = e x from rfl, ringEquivComplexOfIsComplex_norm D w hw x]
    have hballComp : archimedeanUnitBall D w =
        (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw) ⁻¹'
          Metric.closedBall (0 : Complex) 1 := by
      ext x
      simp only [archimedeanUnitBall, Set.mem_setOf_eq, Set.mem_preimage, Metric.mem_closedBall,
        dist_zero_right]
      change ‖x‖ ≤ 1 ↔
        ‖(NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw) x‖ ≤ 1
      rw [show (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw) x
          = NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw x from rfl,
        ringEquivComplexOfIsComplex_norm D w hw x]
    refine
      { moduleK := archimedeanModuleOfIsComplex D w hw
        logShell := archimedeanUnitBall D w
        logShell_subset_unitBall := fun x hx => hx
        zero_mem_logShell := ?_
        convex_logShell := ?_
        isCompact_logShell := ?_ }
    · simp [archimedeanUnitBall]
    · rw [hballConv]
      exact (convex_closedBall (0 : Complex) 1).linear_preimage L
    · rw [hballComp]
      exact
        (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).toHomeomorph.isCompact_preimage.mpr
          (isCompact_closedBall (0 : Complex) 1)
  · have hreal : w.IsReal := NumberField.InfinitePlace.not_isComplex_iff_isReal.mp hw
    letI : Module Real w.Completion := archimedeanModuleOfIsReal D w hreal
    let e := NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hreal
    let L : w.Completion →ₗ[Real] Real :=
      { toFun := fun x => e x
        map_add' := fun x y => map_add e x y
        map_smul' := by
          intro r x
          change e (e.symm r * x) = r * e x
          rw [map_mul, RingEquiv.apply_symm_apply] }
    have hballConv : archimedeanUnitBall D w = L ⁻¹' Metric.closedBall (0 : Real) 1 := by
      ext x
      simp only [archimedeanUnitBall, Set.mem_setOf_eq, Set.mem_preimage, Metric.mem_closedBall,
        dist_zero_right]
      change ‖x‖ ≤ 1 ↔ ‖L x‖ ≤ 1
      rw [show L x = e x from rfl, ringEquivRealOfIsReal_norm D w hreal x]
    have hballComp : archimedeanUnitBall D w =
        (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hreal) ⁻¹'
          Metric.closedBall (0 : Real) 1 := by
      ext x
      simp only [archimedeanUnitBall, Set.mem_setOf_eq, Set.mem_preimage, Metric.mem_closedBall,
        dist_zero_right]
      change ‖x‖ ≤ 1 ↔
        ‖(NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hreal) x‖ ≤ 1
      rw [show (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hreal) x
          = NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hreal x from rfl,
        ringEquivRealOfIsReal_norm D w hreal x]
    refine
      { moduleK := archimedeanModuleOfIsReal D w hreal
        logShell := archimedeanUnitBall D w
        logShell_subset_unitBall := fun x hx => hx
        zero_mem_logShell := ?_
        convex_logShell := ?_
        isCompact_logShell := ?_ }
    · simp [archimedeanUnitBall]
    · rw [hballConv]
      exact (convex_closedBall (0 : Real) 1).linear_preimage L
    · rw [hballComp]
      exact
        (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hreal).toHomeomorph.isCompact_preimage.mpr
          (isCompact_closedBall (0 : Real) 1)

/-- The actual archimedean log-shell family over all infinite places of
`Fmod`: an inhabitant of S1927's `S1927FirstMissing D`. -/
noncomputable def paperArchimedeanLogShell (D : S1895PaperInput) :
    S1927FirstMissing D :=
  fun w => paperArchimedeanLogShellDatum D w

/-- The constructed datum uses the actual closed unit ball as its log-shell. -/
@[simp] theorem paperArchimedeanLogShell_logShell :
    (paperArchimedeanLogShell D w).logShell = archimedeanUnitBall D w := by
  by_cases hw : w.IsComplex
  · simp [paperArchimedeanLogShell, paperArchimedeanLogShellDatum, hw]
  · simp [paperArchimedeanLogShell, paperArchimedeanLogShellDatum, hw]

/-- The constructed log-shell is the actual metric closed unit ball. -/
theorem paperArchimedeanLogShell_logShell_eq_closedBall :
    (paperArchimedeanLogShell D w).logShell = Metric.closedBall (0 : w.Completion) 1 := by
  rw [paperArchimedeanLogShell_logShell, archimedeanUnitBall_eq_closedBall]

/-- The constructed log-shell contains zero, as required by the datum. -/
theorem zero_mem_paperArchimedeanLogShell :
    (0 : w.Completion) ∈ (paperArchimedeanLogShell D w).logShell := by
  rw [paperArchimedeanLogShell_logShell]
  simp [archimedeanUnitBall]

/-- The constructed log-shell contains the unit `1`, so it is not the
degenerate singleton `{0}`. -/
theorem one_mem_paperArchimedeanLogShell :
    (1 : w.Completion) ∈ (paperArchimedeanLogShell D w).logShell := by
  rw [paperArchimedeanLogShell_logShell]
  simp [archimedeanUnitBall]

/-- The constructed set is nontrivial: it simultaneously contains `0` and
`1`, which are distinct in the completion field. -/
theorem paperArchimedeanLogShell_nontrivial :
    (0 : w.Completion) ≠ 1 ∧
      (0 : w.Completion) ∈ (paperArchimedeanLogShell D w).logShell ∧
      (1 : w.Completion) ∈ (paperArchimedeanLogShell D w).logShell :=
  ⟨zero_ne_one, zero_mem_paperArchimedeanLogShell D w, one_mem_paperArchimedeanLogShell D w⟩

/-- The constructed log-shell is contained in the actual closed unit ball. -/
theorem paperArchimedeanLogShell_subset_unitBall :
    (paperArchimedeanLogShell D w).logShell ⊆ archimedeanUnitBall D w := by
  intro x hx
  rw [paperArchimedeanLogShell_logShell] at hx
  exact hx

/-- S1927's archimedean first missing type is inhabited for every S1895 paper
input: the exact first missing object recorded in S1927 is not an obstruction. -/
theorem s1950FirstMissing_inhabited (D : S1895PaperInput) :
    Nonempty (S1927FirstMissing D) :=
  ⟨paperArchimedeanLogShell D⟩

/-- Assembly of the full log-Kummer package from the constructed archimedean
log-shell and the Kummer evaluation square alone. -/
noncomputable def paperFullLogKummerUQOfKummerSquare
    (D : S1895PaperInput) (square : S1927KummerEvaluationSquareActual D) :
    S1927FullLogKummerUQ D :=
  s1927FullLogKummerUQ_of_missing D (paperArchimedeanLogShell D) square

/-- The exact remaining missing input of the full log-Kummer package is the
Kummer evaluation square: the full package is inhabited if and only if the
Kummer evaluation square is.  The archimedean log-shell component is supplied
by `paperArchimedeanLogShell`. -/
theorem paperFullLogKummerUQ_nonempty_iff_kummerSquare_nonempty
    (D : S1895PaperInput) :
    Nonempty (S1927FullLogKummerUQ D) ↔
      Nonempty (S1927KummerEvaluationSquareActual D) := by
  constructor
  · rintro ⟨package⟩
    exact ⟨package.evaluationSquare⟩
  · rintro ⟨square⟩
    exact ⟨paperFullLogKummerUQOfKummerSquare D square⟩

/-! ## Axiom probes -/

#print axioms paperArchimedeanLogShellDatum
#print axioms paperArchimedeanLogShell
#print axioms paperArchimedeanLogShell_nontrivial
#print axioms paperFullLogKummerUQOfKummerSquare
#print axioms paperFullLogKummerUQ_nonempty_iff_kummerSquare_nonempty

end LeanFormal.IUT.XiFPaper.S1950ArchimedeanLogShellActual
