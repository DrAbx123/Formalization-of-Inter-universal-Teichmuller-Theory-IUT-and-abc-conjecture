import LeanFormal.IUT.IUTII.Kummer.SourceLogShellCarrier
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# N8 group 2 — log-carrier descent criterion

Stage-2 statement for the source log carrier `SourceLogShellDatum`.

Consumer: this is the chapter-C quotient/descent prerequisite for a future
K1 construction carrying actual `D.Units`/`D.logMap` instead of the abstract
`Choice` index.  It does not identify `D.logMap` with the p-adic log, and does
not build K1/K2 records.

Proof: the reverse direction is the universal property of the quotient by the
log kernel; forward direction is well-definedness on log fibers.
-/

namespace LeanFormal.IUT

universe u

/-- A function `f` on `D.Units` descends to the log range iff it is constant on
kernel cosets.  This is the exact chapter-C descent criterion for the source
log-shell datum. -/
theorem SourceLogShellDatum.descends_iff
    (D : SourceLogShellDatum) {Y : Type u}
    (f : D.Units → Y) :
    (∃ fbar : D.logMap.range → Y,
      ∀ u : D.Units,
        fbar ⟨D.logMap u, ⟨u, rfl⟩⟩ = f u) ↔
    (∀ (u t : D.Units), t ∈ D.logMap.ker → f (t * u) = f u) := by
  constructor
  · rintro ⟨fbar, hbar⟩ u t ht
    have hlog : D.logMap (t * u) = D.logMap u := by
      rw [map_mul, MonoidHom.mem_ker.mp ht, one_mul]
    calc
      f (t * u) = fbar ⟨D.logMap (t * u), ⟨t * u, rfl⟩⟩ := (hbar (t * u)).symm
      _ = fbar ⟨D.logMap u, ⟨u, rfl⟩⟩ := by
            congr 1
            exact Subtype.ext hlog
      _ = f u := hbar u
  · intro h
    let pick : D.logMap.range → D.Units := fun y => Classical.choose y.2
    have pick_spec : ∀ y : D.logMap.range, D.logMap (pick y) = y.1 :=
      fun y => Classical.choose_spec y.2
    let fbar : D.logMap.range → Y := fun y => f (pick y)
    refine ⟨fbar, ?_⟩
    intro u
    have hmem : D.logMap u ∈ D.logMap.range := ⟨u, rfl⟩
    have hker : (pick ⟨D.logMap u, hmem⟩)⁻¹ * u ∈ D.logMap.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, pick_spec ⟨D.logMap u, hmem⟩,
        inv_mul_cancel]
    have hh := h (pick ⟨D.logMap u, hmem⟩) ((pick ⟨D.logMap u, hmem⟩)⁻¹ * u) hker
    dsimp [fbar]
    -- hh : f ((pick ...)⁻¹ * u * pick ...) = f (pick ...)
    -- simplify the argument to f on the left
    have harg : (pick ⟨D.logMap u, hmem⟩)⁻¹ * u * pick ⟨D.logMap u, hmem⟩ = u := by
      simp [mul_assoc, mul_comm, mul_left_comm]
    rw [harg] at hh
    exact hh.symm

end LeanFormal.IUT