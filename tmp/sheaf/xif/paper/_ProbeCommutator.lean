import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.IndexNormal
open scoped commutatorElement
variable {G : Type*} [Group G] (P M L : Subgroup G)
#check Subgroup.commutator
#check ⁅P, M⁆
#check Subgroup.commutator_mono
#check Subgroup.Normal.quotient_commutative_iff_commutator_le
#check Subgroup.normal_of_index_eq_two
#check Subgroup.subgroupOf
#check Subgroup.index_eq_one
#check Subgroup.eq_top_of_index_eq_one
#check Subgroup.commutator_eq_top
