import LeanFormal.IUT.Foundations.LocalFields.IntegralUnits

/-!
# ShehddIntegralUnitsChainActual — integral units/norm-one chain

New chain consequences of the compiled integral-unit laws: integral units have norm one
and lie in the integer ring, the norm-one homeomorphism is realized by `unitOfNormOne`, and
the unit group is compact with open principal units.  No new assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddIntegralUnitsChainActual

open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldIntegralUnits

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- **PROVED chain:** an integral unit lies in the integer ring and has norm one. -/
theorem unit_norm_and_integer_chain (u : (Integers K)ˣ) :
    ((u.val : K) ∈ Integers K) ∧ ‖(u.val : K)‖ = 1 := by
  refine ⟨?_, norm_unit_eq_one u⟩
  rw [mem_integers_iff]
  exact le_of_eq (norm_unit_eq_one u)

/-- **PROVED chain:** the norm-one element built from a unit of norm one is a unit with
that underlying element and norm one. -/
theorem unitOfNormOne_chain (x : {x : K | ‖x‖ = 1}) :
    ((unitOfNormOne x).val : K) = x ∧ ‖((unitOfNormOne x).val : K)‖ = 1 := by
  have hx : ((unitOfNormOne x).val : K) = x := rfl
  exact ⟨hx, by rw [hx]; exact x.property⟩

/-- **PROVED chain:** under properness the unit group is compact and the principal units
are open. -/
theorem units_topology_chain [ProperSpace K] :
    CompactSpace (Integers K)ˣ ∧
      IsOpen (principalUnits (K := K) : Set (Integers K)ˣ) :=
  ⟨compactSpace_units (K := K), isOpen_principalUnits (K := K)⟩

end LeanFormal.IUT.XiFPaper.ShehddIntegralUnitsChainActual
end
