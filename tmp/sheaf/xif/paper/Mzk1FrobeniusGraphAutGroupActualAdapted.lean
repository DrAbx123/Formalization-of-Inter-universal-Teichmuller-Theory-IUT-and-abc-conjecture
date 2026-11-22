/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1FrobeniusGraphAutClosureActual

/-!
# Frobenius-picture graph: the automorphism group as a Subgroup (IUTI HodgeTheater)

Declaration-level addendum: packaging the graph automorphisms of the Frobenius-picture
oriented graph Gamma as a subgroup of the permutation group of the vertex set Z,
together with the translation membership theorem (Aut(Gamma) contains the translations).
This is the group-object form used when comparing the theta-link group actions.

SHEAF node: iuti-ii:HodgeThetaLinkGraph.group (kind theorem, status PENDING-VERIFY
until the DAG watchdog reports EXIT0).  No new axioms.
-/

namespace LeanFormal.IUT

/-- The automorphism group of the Frobenius-picture graph, as a subgroup of the
permutation group of Z. -/
def frobeniusGraphAutGroup : Subgroup (Equiv.Perm Int) where
  carrier := { sigma | FrobeniusPictureGraphAut sigma }
  one_mem' := graphAut_one
  mul_mem' := fun h1 h2 => FrobeniusPictureGraphAut_mul h1 h2
  inv_mem' := fun h => FrobeniusPictureGraphAut_inv h

/-- Membership in the graph automorphism group is the graph automorphism predicate. -/
theorem mem_frobeniusGraphAutGroup {sigma : Equiv.Perm Int} :
    sigma ∈ frobeniusGraphAutGroup ↔ FrobeniusPictureGraphAut sigma := Iff.rfl

/-- Every translation is an element of the graph automorphism group. -/
theorem chainTranslation_mem_graphAutGroup (k : Int) :
    chainTranslation k ∈ frobeniusGraphAutGroup := chainTranslation_graphAut k

/-- The graph automorphism group is a group, so its carrier is closed under the group
operations (recorded for consumers). -/
theorem frobeniusGraphAutGroup_inv_mem {sigma : Equiv.Perm Int}
    (h : sigma ∈ frobeniusGraphAutGroup) : sigma⁻¹ ∈ frobeniusGraphAutGroup :=
  frobeniusGraphAutGroup.inv_mem h

/-- The graph automorphism group consists exactly of the translations. -/
theorem frobeniusGraphAutGroup_mem_iff_range {sigma : Equiv.Perm Int} :
    sigma ∈ frobeniusGraphAutGroup ↔ ∃ k : Int, sigma = chainTranslation k := by
  rw [mem_frobeniusGraphAutGroup]
  exact graphAut_eq_translation sigma

/-- The carrier of the graph automorphism group is the range of the translation map. -/
theorem frobeniusGraphAutGroup_coe_eq_range :
    (frobeniusGraphAutGroup : Set (Equiv.Perm Int)) = Set.range chainTranslation := by
  ext sigma
  rw [SetLike.mem_coe, frobeniusGraphAutGroup_mem_iff_range, Set.mem_range]

end LeanFormal.IUT