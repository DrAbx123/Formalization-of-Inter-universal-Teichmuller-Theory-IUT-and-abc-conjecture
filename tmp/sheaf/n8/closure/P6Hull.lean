import Mathlib

/-!
# P6 hull: exact source-region types and inclusions

This file defines the P6 region package abstractly over an actual carrier X:

* R_alpha : Alpha -> Set X;
* U = union_alpha R_alpha;
* H = paperHull, with the exact equation H = paperHullOp U and paperHullOp
  extensive/monotone/idempotent;
* HullPoss = {R | Adm_out R and R subset H}.

The paper hull operation is carried as explicit data (PaperHullOperator); it is
NOT replaced by any canonical hull.  No canonicalHull import is used.  The exact
source instantiation of R_alpha/Adm_out/paperHullOp is a separate donor and is
not asserted here.
-/

namespace LeanFormal.IUT.N8Closure.P6Hull

universe u v

/-- A paper hull operator on a carrier: extensive, monotone, idempotent. -/
structure PaperHullOperator (X : Type u) where
  hull : Set X → Set X
  extensive : ∀ S : Set X, S ⊆ hull S
  monotone : ∀ {S T : Set X}, S ⊆ T → hull S ⊆ hull T
  idempotent : ∀ S : Set X, hull (hull S) = hull S

/-- The exact P6 source-region package. -/
structure P6HullSetup where
  /-- The actual carrier of regions. -/
  X : Type u
  /-- Index of the source output family R_alpha. -/
  Alpha : Type v
  /-- The source output regions R_alpha. -/
  R : Alpha → Set X
  /-- The source admissibility predicate Adm_out on regions. -/
  adm_out : Set X → Prop
  /-- The paper hull operator, not the canonical hull. -/
  paperHullOp : PaperHullOperator X
  /-- The paper hull H. -/
  paperHull : Set X
  /-- Exact definition of H from the paper hull operator applied to U. -/
  paperHull_eq : paperHull = paperHullOp.hull (⋃ a : Alpha, R a)

namespace P6HullSetup

variable (D : P6HullSetup.{u, v})

/-- The union U = union_alpha R_alpha. -/
def U : Set D.X :=
  ⋃ a : D.Alpha, D.R a

/-- H = paper hull of U; this is the exact paperHull field, not canonicalHull. -/
def H : Set D.X :=
  D.paperHull

/-- HullPoss = {R | Adm_out R and R subset H}.  This is the exact set-builder,
with no free allowed-subset field. -/
def HullPoss : Set (Set D.X) :=
  {R | D.adm_out R ∧ R ⊆ D.H}

/-- Each R_alpha is contained in the union U. -/
theorem R_subset_U (a : D.Alpha) : D.R a ⊆ D.U := by
  intro x hx
  exact Set.mem_iUnion.mpr ⟨a, hx⟩

/-- The union U is exactly the union of the R_alpha. -/
theorem mem_U_iff {x : D.X} :
    x ∈ D.U ↔ ∃ a : D.Alpha, x ∈ D.R a :=
  Set.mem_iUnion

/-- The union U is contained in the paper hull H. -/
theorem U_subset_H : D.U ⊆ D.H := by
  intro x hx
  change x ∈ D.paperHull
  rw [D.paperHull_eq]
  exact D.paperHullOp.extensive _ hx

/-- Each source region R_alpha is contained in H. -/
theorem R_subset_H (a : D.Alpha) : D.R a ⊆ D.H :=
  (D.R_subset_U a).trans D.U_subset_H

/-- Membership in HullPoss is exactly admissibility plus containment in H. -/
theorem mem_HullPoss_iff {R : Set D.X} :
    R ∈ D.HullPoss ↔ D.adm_out R ∧ R ⊆ D.H :=
  Iff.rfl

/-- HullPoss is a subfamily of the regions contained in H. -/
theorem HullPoss_subset_regions_contained_in_H :
    D.HullPoss ⊆ {R : Set D.X | R ⊆ D.H} := by
  intro R hR
  exact hR.2

/-- If H itself is admissible, H belongs to HullPoss. -/
theorem H_mem_HullPoss (hH : D.adm_out D.H) : D.H ∈ D.HullPoss :=
  ⟨hH, subset_rfl⟩

/-- The paper hull is monotone in U: a larger source family has a larger hull. -/
theorem paperHull_monotone {S : Set D.X} (hS : S ⊆ D.U) :
    D.paperHullOp.hull S ⊆ D.H := by
  change D.paperHullOp.hull S ⊆ D.paperHull
  rw [D.paperHull_eq]
  exact D.paperHullOp.monotone hS

end P6HullSetup

end LeanFormal.IUT.N8Closure.P6Hull
