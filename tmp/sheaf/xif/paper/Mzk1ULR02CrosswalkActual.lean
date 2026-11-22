/- R0.2 crosswalk interface skeleton (per Lead 2026-11-18; no proof of the crosswalk itself).

The paper full-fiber coefficient is `cPFullFiber_b := (1/[F:Q]) Σ_{P|b} f_P v_P(q_P)`;
R0.2 states the per-b crosswalk to the local R0.1 coefficient `cP_local = v_P/e_P^abs`:
  cPFullFiber_b = ([Fmod_b:Q_p]/[Fmod:Q]) * cP_local.
This file provides the interface/structure carrying that hypothesis, so downstream
consumers (`MpaperB = -qPilotMass cPFullFiber` definitional) can take `hper :
∀ b, MpaperB b = -qPilotMass (cPFullFiber b)` with `cPFullFiber := ...`.
-/
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1ULR02CrosswalkActual

open scoped BigOperators

/-- R0.2 per-b crosswalk data: full-fiber coefficient, local coefficient (v_P/e_abs),
the local degree [Fmod_b:Q_p] and d_mod=[Fmod:Q], with the paper crosswalk as a field. -/
structure R02CrosswalkData (ι : Type*) where
  /-- the paper full-fiber coefficient per b. -/
  cPFullFiber : ι → ℝ
  /-- the R0.1 local coefficient v_P/e_P^abs per b. -/
  cP_local : ι → ℝ
  /-- the local degree [Fmod_b:Q_p]. -/
  fmodLocalDegree : ι → ℝ
  /-- d_mod = [Fmod:Q]. -/
  dMod : ℝ
  dMod_pos : 0 < dMod
  /-- R0.2 per-b crosswalk (paper formula). -/
  crosswalk : ∀ b, cPFullFiber b = (fmodLocalDegree b / dMod) * cP_local b

/-- PROVED: nonneg full-fiber coefficient from nonneg local data and degrees. -/
theorem R02CrosswalkData.cPFullFiber_nonneg {ι : Type*} (D : R02CrosswalkData ι)
    (hdeg : ∀ b, 0 ≤ D.fmodLocalDegree b) (hloc : ∀ b, 0 ≤ D.cP_local b) :
    ∀ b, 0 ≤ D.cPFullFiber b := by
  intro b
  rw [D.crosswalk b]
  exact mul_nonneg (div_nonneg (hdeg b) (le_of_lt D.dMod_pos)) (hloc b)

/-- PROVED: rewriting the crosswalk in the direction used by R0.2 consumers. -/
theorem R02CrosswalkData.crosswalk' {ι : Type*} (D : R02CrosswalkData ι) (b : ι) :
    D.cPFullFiber b = D.fmodLocalDegree b / D.dMod * D.cP_local b :=
  D.crosswalk b

end LeanFormal.IUT.XiFPaper.Mzk1ULR02CrosswalkActual
end
