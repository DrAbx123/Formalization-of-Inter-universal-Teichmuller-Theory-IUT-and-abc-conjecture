import Mathlib

import tmp.sheaf.xif.paper.Hull01DefinitionActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# STEP 0 prior-art: closure operator|hull operator|actualHolomorphicHull -> hits tmp/sheaf/xif/paper/Hull01DefinitionActual (HullSystem/hull/least/unique) + C3LogShellTensorHolomorphicHullActual:76/82/93 (concrete hull + containment/leastness) -> ADAPT (closure-operator laws P1-P3; no re-proof of concrete facts).

# [Hull] 02: closure-operator laws for the holomorphic hull (IUT III Rem 3.9.5(ii)) - class A

Corpus: papers/motizuki_corpus/text/Inter-universal Teichmuller Theory III.txt,
Remark 3.9.5(ii): the hull construction gives a closure operator phi with the
properties (P1) extensive: P subset phi(P); (P2) monotone; (P3) idempotent:
phi(phi(P)) = phi(P); compatible with the inclusion preorder.  This file proves
P1-P3 abstractly from the hull-system definition (Hull01), plus the least-closed-
superset and fixed-point (closed) characterization.  Class A; no closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Hull02ClosureOperatorActual

open LeanFormal.IUT.XiFPaper.Hull01DefinitionActual

universe u

variable {X : Type u} (HS : HullSystem X)

/-- The closure operator: phi(P) = hull(P). -/
def phi : Set X → Set X := HS.hull

/-- **(P1) Extensive:** P is contained in phi(P). -/
theorem phi_extensive (P : Set X) : P ⊆ phi HS P := HS.subset_hull P

/-- **(P2) Monotone** with respect to inclusion. -/
theorem phi_monotone : Monotone (phi HS) := fun _ _ h => HS.hull_mono h

/-- **(P3) Idempotent:** phi(phi(P)) = phi(P). -/
theorem phi_idempotent (P : Set X) : phi HS (phi HS P) = phi HS P := HS.hull_idem P

/-- The three closure-operator laws packaged. -/
theorem phi_laws :
    (∀ P : Set X, P ⊆ phi HS P) ∧ Monotone (phi HS) ∧
      (∀ P : Set X, phi HS (phi HS P) = phi HS P) :=
  ⟨phi_extensive HS, phi_monotone HS, phi_idempotent HS⟩

/-- A set is closed when it is a fixed point of phi. -/
def Closed (P : Set X) : Prop := phi HS P = P

/-- phi(P) is always closed. -/
theorem phi_closed (P : Set X) : Closed HS (phi HS P) :=
  phi_idempotent HS P

/-- Closed sets are exactly the scaled regions (family members). -/
theorem closed_iff_family (P : Set X) : Closed HS P ↔ HS.Family P := by
  constructor
  · intro h
    have hm := HS.hull_mem_family P
    rw [Closed, phi] at h
    rwa [h] at hm
  · intro hF
    apply Set.Subset.antisymm
    · exact HS.hull_subset P P hF (Set.Subset.refl P)
    · exact HS.subset_hull P

/-- **(P1') Least closed superset:** phi(P) is contained in every closed set
containing P. -/
theorem phi_least_closed (P H : Set X) (hF : HS.Family H) (hP : P ⊆ H) :
    phi HS P ⊆ H :=
  HS.hull_subset P H hF hP

#check phi
#check phi_extensive
#check phi_monotone
#check phi_idempotent
#check phi_laws
#check Closed
#check phi_closed
#check closed_iff_family
#check phi_least_closed

end LeanFormal.IUT.XiFPaper.Hull02ClosureOperatorActual