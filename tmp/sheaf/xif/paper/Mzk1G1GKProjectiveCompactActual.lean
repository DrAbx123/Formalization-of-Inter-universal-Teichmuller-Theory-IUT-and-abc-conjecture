/- GK §7.3 projective compactness: normalized unit sphere and Fermat sphere in `K^3`
(route L683). -/
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Topology.Algebra.WithZeroTopology
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic

noncomputable section
open scoped Valued WithZeroTopology
open ValuativeRel
namespace LeanFormal.IUT.XiFPaper.Mzk1G1GKProjectiveCompactActual

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The integral unit ball of `K^3`: all coordinates have valuation at most one. -/
def unitBall : Set (Fin 3 → K) :=
  Set.univ.pi (fun _ : Fin 3 => {x : K | valuation K x ≤ 1})

/-- The normalized unit sphere of `K^3`: integral, and some coordinate has valuation
exactly one. -/
def unitSphere : Set (Fin 3 → K) :=
  unitBall (K := K) ∩ {v | ∃ i, valuation K (v i) = 1}

/-- The integral unit ball is compact (finite product of compact closed balls). -/
theorem isCompact_unitBall : IsCompact (unitBall (K := K)) :=
  isCompact_univ_pi (fun _ =>
    IsNonarchimedeanLocalField.isCompact_closedBall (K := K) (1 : ValueGroupWithZero K))

/-- The set of vectors with some coordinate of valuation exactly one is closed. -/
theorem isClosed_exists_valuation_eq_one :
    IsClosed {v : Fin 3 → K | ∃ i, valuation K (v i) = 1} := by
  haveI : T2Space (ValueGroupWithZero K) := inferInstance
  have hclosed : ∀ i : Fin 3, IsClosed {v : Fin 3 → K | valuation K (v i) = 1} := by
    intro i
    have hcont : Continuous (fun v : Fin 3 → K => valuation K (v i)) :=
      (IsValuativeTopology.continuous_valuation (R := K)).comp (continuous_apply i)
    exact isClosed_eq hcont continuous_const
  rw [show {v : Fin 3 → K | ∃ i, valuation K (v i) = 1}
      = ⋃ i : Fin 3, {v : Fin 3 → K | valuation K (v i) = 1} from by
        ext v
        simp]
  exact isClosed_iUnion_of_finite hclosed

/-- The unit sphere is a subset of the integral unit ball. -/
theorem unitSphere_subset_unitBall : unitSphere (K := K) ⊆ unitBall (K := K) :=
  fun v hv => hv.1

/-- A unit-sphere point is nonzero. -/
theorem unitSphere_ne_zero {v : Fin 3 → K} (hv : unitSphere (K := K) v) : v ≠ 0 := by
  obtain ⟨-, i, hi⟩ := hv
  rintro rfl
  simpa using hi

/-- The unit sphere is closed (in a T2 local field: compact sets are closed). -/
theorem isClosed_unitSphere [T2Space K] : IsClosed (unitSphere (K := K)) := by
  have h := isClosed_exists_valuation_eq_one.inter (isCompact_unitBall (K := K)).isClosed
  simpa [unitSphere, Set.inter_comm] using h

/-- **Compactness of the normalized unit sphere** (route L683). -/
theorem isCompact_unitSphere [T2Space K] : IsCompact (unitSphere (K := K)) :=
  (isCompact_unitBall (K := K)).of_isClosed_subset (isClosed_unitSphere (K := K))
    unitSphere_subset_unitBall

section Fermat

variable {n : Nat}

/-- The Fermat condition `v0^n + v1^n = v2^n` is closed (polynomial equation). -/
theorem isClosed_fermatCondition [T2Space K] :
    IsClosed {v : Fin 3 → K | v 0 ^ n + v 1 ^ n = v 2 ^ n} := by
  have hcont : Continuous (fun v : Fin 3 → K => v 0 ^ n + v 1 ^ n - v 2 ^ n) := by
    fun_prop
  have h := isClosed_eq hcont (continuous_const : Continuous fun _ : Fin 3 → K => (0 : K))
  simpa [sub_eq_zero] using h

/-- The Fermat sphere of normalized coordinates. -/
def Ysphere : Set (Fin 3 → K) :=
  unitSphere (K := K) ∩ {v | v 0 ^ n + v 1 ^ n = v 2 ^ n}

/-- The Fermat sphere is closed. -/
theorem isClosed_Ysphere [T2Space K] : IsClosed (Ysphere (K := K) (n := n)) := by
  have h := (isClosed_fermatCondition (K := K) (n := n)).inter (isClosed_unitSphere (K := K))
  simpa [Ysphere, Set.inter_comm] using h

/-- **Compactness of the Fermat sphere** `Y_n(K)` in normalized coordinates. -/
theorem isCompact_Ysphere [T2Space K] : IsCompact (Ysphere (K := K) (n := n)) :=
  (isCompact_unitSphere (K := K)).of_isClosed_subset (isClosed_Ysphere (K := K) (n := n))
    (fun v hv => hv.1)

/-- The unit action of `𝒪[K]ˣ` on normalized vectors. -/
def unitAction (u : 𝒪[K]ˣ) (v : Fin 3 → K) : Fin 3 → K :=
  fun i => (u : K) * v i

/-- The projective relation: normalized vectors modulo the unit action. -/
def projRel (v w : Fin 3 → K) : Prop :=
  ∃ u : 𝒪[K]ˣ, w = unitAction u v

end Fermat

#print axioms isCompact_unitBall
#print axioms isClosed_exists_valuation_eq_one
#print axioms isClosed_unitSphere
#print axioms isClosed_Ysphere
#print axioms isCompact_unitSphere
#print axioms isClosed_fermatCondition
#print axioms isCompact_Ysphere
end LeanFormal.IUT.XiFPaper.Mzk1G1GKProjectiveCompactActual