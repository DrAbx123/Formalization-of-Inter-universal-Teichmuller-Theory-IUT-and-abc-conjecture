/- Ported from LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceHolomorphicDifferentBase.lean
(traceDual_one_le_one_self, differentIdeal_self_eq_top) into the alan lane to avoid importing the
core file (which currently has errors). -/
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1UniversalDifferentSelfActual

open Submodule

universe u

/-- In the self-extension K/A the trace dual of the unit submodule is contained in the unit
submodule. -/
theorem traceDual_one_le_one_self {A K : Type*} [CommRing A] [Field K] [Algebra A K] :
    Submodule.traceDual A K (1 : Submodule A K) ≤ 1 := by
  intro x hx
  rw [Submodule.mem_one]
  have hx' :=
    (Submodule.mem_traceDual (A := A) (K := K) (L := K) (B := A)
      (I := (1 : Submodule A K))).mp hx 1
      (Submodule.mem_one.mpr ⟨1, map_one (algebraMap A K)⟩)
  rw [Algebra.traceForm_apply, mul_one, Algebra.trace_self_apply] at hx'
  exact hx'

/-- The different ideal of a Dedekind domain over itself is the unit ideal. -/
theorem differentIdeal_self_eq_top (A : Type*) [CommRing A] [IsDedekindDomain A] :
    differentIdeal A A = ⊤ := by
  rw [Ideal.eq_top_iff_one, differentIdeal, Submodule.mem_comap]
  change algebraMap A (FractionRing A) 1 ∈
    (1 : Submodule A (FractionRing A)) /
      Submodule.traceDual A (FractionRing A) 1
  rw [map_one, Submodule.one_mem_div]
  exact traceDual_one_le_one_self (A := A) (K := FractionRing A)

#print axioms traceDual_one_le_one_self
#print axioms differentIdeal_self_eq_top
end LeanFormal.IUT.XiFPaper.Mzk1G1UniversalDifferentSelfActual
