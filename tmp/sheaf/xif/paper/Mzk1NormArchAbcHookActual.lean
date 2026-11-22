/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1NormArchCKActual
import tmp.sheaf.xif.paper.Mzk1ArchFactorDegreeOneActual

/-! # GAP-NORM-ARCH-C-K / abc docking type table (task #10 follow-up)

Explicit interface between the proved `archCK K = 1/[K:Q]` and the abc
C3/S1902 `haarScale` output.  The equality `haarScale = archCK K` is a
named input, not proved: the current C3S1902 HaarScaleData only stores an
arbitrary positive `haarScale` without an arch-degree formula. -/
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1NormArchAbcHookActual
open LeanFormal.IUT.XiFPaper.Mzk1NormArchCKActual
variable {K : Type*} [Field K] [NumberField K]

/-- Explicit abc-side arch factor output, with its defining equations to
the proved `archCK`/`archCKToric`. -/
structure AbcArchFactorOutput (K : Type*) [Field K] [NumberField K] where
  archFactor : ℝ
  toricArchFactor : ℝ
  archFactor_eq : archFactor = archCK K
  toricArchFactor_eq : toricArchFactor = archCKToric K

theorem AbcArchFactorOutput.archFactor_def
    (O : AbcArchFactorOutput K) : O.archFactor = archCK K := O.archFactor_eq
theorem AbcArchFactorOutput.toricArchFactor_def
    (O : AbcArchFactorOutput K) : O.toricArchFactor = archCKToric K := O.toricArchFactor_eq

/-- Named docking input: abc C3/S1902 `haarScale` is the explicit `C_K`. -/
structure C3HaarScaleDocking (K : Type*) [Field K] [NumberField K] where
  haarScale : ℝ
  haarScale_pos : 0 < haarScale
  haarScale_eq_archCK : haarScale = archCK K

theorem C3HaarScaleDocking.haarScale_eq
    (D : C3HaarScaleDocking K) : D.haarScale = archCK K := D.haarScale_eq_archCK
theorem C3HaarScaleDocking.haarScale_pos'
    (D : C3HaarScaleDocking K) : 0 < D.haarScale := D.haarScale_pos


/-- Concrete degree-one instantiation: `[K:Q]=1` gives `C_K=1`, so the
docking value `haarScale=1` is available. -/
theorem C3HaarScaleDocking_nonempty_of_finrank_one
    (h : Module.finrank ℚ K = 1) : Nonempty (C3HaarScaleDocking K) := by
  refine ⟨{ haarScale := 1, haarScale_pos := one_pos, haarScale_eq_archCK := ?_ }⟩
  rw [archCK_eq_heightWeight]
  exact (LeanFormal.IUT.XiFPaper.Mzk1NormArchCAbcActual.heightWeight_eq_one_of_finrank_one h).symm

/-- The abc arch-factor output type is inhabited by the proved `C_K` values. -/
theorem AbcArchFactorOutput_nonempty : Nonempty (AbcArchFactorOutput K) := by
  exact ⟨archCK K, archCKToric K, rfl, rfl⟩

def normArchAbcHookRows : List (String × String) :=
  [ ("AbcArchFactorOutput", "type-table: archFactor/toricArchFactor = C_K"),
    ("C3HaarScaleDocking", "named input: abc haarScale = C_K"),
    ("docking proof", "GAP: C3S1902HaarScaleData has no arch-degree formula") ]
theorem normArchAbcHookRows_length : normArchAbcHookRows.length = 3 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1NormArchAbcHookActual
