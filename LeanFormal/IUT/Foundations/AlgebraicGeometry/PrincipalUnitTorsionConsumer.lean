import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceSourceLogKernel
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceSourceLogShell
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedIntegers
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnits
import Mathlib.Tactic

/-!
# Principal-unit torsion consumer at an arbitrary finite place

The actual completed valuation units have torsion exactly the kernel of the
actual completion logarithm (production FinitePlaceSourceLogKernel).  This
file restricts that statement to the principal-unit subgroup used by the DVR
refinement, records the principal torsion subgroup, and exposes the torsion
quotient injection.  No card, no new source input, and no placeholder.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

noncomputable section

namespace LeanFormal.IUT.PrincipalUnitTorsionConsumer

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open scoped Valued

variable {F : Type*} [Field F] [NumberField F]

variable (v : NumberField.FinitePlace F)

/-- Actual principal units of the completed valuation ring, transported from
the normalized principal units. -/
noncomputable def sourcePrincipalUnits : Subgroup (CompletionIntegers v)ˣ :=
  (principalUnits (K := NormalizedCompletion v)).comap
    (normalizedCompletionUnitsEquiv v).symm.toMonoidHom

theorem mem_sourcePrincipalUnits_iff
    (u : (CompletionIntegers v)ˣ) :
    u ∈ sourcePrincipalUnits v ↔
      (normalizedCompletionUnitsEquiv v).symm u ∈
        principalUnits (K := NormalizedCompletion v) :=
  Subgroup.mem_comap

/-- The principal torsion subgroup: finite-order actual units which are also
principal. -/
noncomputable def sourcePrincipalTorsion : Subgroup (CompletionIntegers v)ˣ :=
  (CommGroup.torsion (CompletionIntegers v)ˣ : Subgroup (CompletionIntegers v)ˣ) ⊓
    sourcePrincipalUnits v

theorem mem_sourcePrincipalTorsion_iff
    (u : (CompletionIntegers v)ˣ) :
    u ∈ sourcePrincipalTorsion v ↔
      IsOfFinOrder u ∧ u ∈ sourcePrincipalUnits v := by
  rw [sourcePrincipalTorsion, Subgroup.mem_inf]
  change IsOfFinOrder u ∧ u ∈ sourcePrincipalUnits v ↔ _
  exact Iff.rfl

theorem sourcePrincipalTorsion_le_sourcePrincipalUnits :
    (sourcePrincipalTorsion v : Subgroup (CompletionIntegers v)ˣ) ≤
      sourcePrincipalUnits v :=
  inf_le_right

theorem sourcePrincipalTorsion_le_torsion :
    (sourcePrincipalTorsion v : Subgroup (CompletionIntegers v)ˣ) ≤
      (CommGroup.torsion (CompletionIntegers v)ˣ :
        Subgroup (CompletionIntegers v)ˣ) :=
  inf_le_left

theorem sourcePrincipalTorsion_one_mem :
    (1 : (CompletionIntegers v)ˣ) ∈ sourcePrincipalTorsion v := by
  rw [mem_sourcePrincipalTorsion_iff]
  exact ⟨IsOfFinOrder.one, (sourcePrincipalUnits v).one_mem⟩

theorem sourcePrincipalTorsion_inv_mem
    {u : (CompletionIntegers v)ˣ} (hu : u ∈ sourcePrincipalTorsion v) :
    u⁻¹ ∈ sourcePrincipalTorsion v := by
  rw [mem_sourcePrincipalTorsion_iff] at hu ⊢
  exact ⟨hu.1.inv, (sourcePrincipalUnits v).inv_mem hu.2⟩

theorem sourcePrincipalTorsion_mul_mem
    {u w : (CompletionIntegers v)ˣ}
    (hu : u ∈ sourcePrincipalTorsion v) (hw : w ∈ sourcePrincipalTorsion v) :
    u * w ∈ sourcePrincipalTorsion v := by
  rw [mem_sourcePrincipalTorsion_iff] at hu hw ⊢
  exact ⟨hu.1.mul hw.1, (sourcePrincipalUnits v).mul_mem hu.2 hw.2⟩

theorem sourcePrincipalTorsion_pow_mem
    {u : (CompletionIntegers v)ˣ} (hu : u ∈ sourcePrincipalTorsion v) (n : Nat) :
    u ^ n ∈ sourcePrincipalTorsion v := by
  rw [mem_sourcePrincipalTorsion_iff] at hu ⊢
  exact ⟨hu.1.pow (n := n), (sourcePrincipalUnits v).pow_mem hu.2 n⟩

/-- On principal units, finite order is exactly vanishing of the actual
completed logarithm. -/
theorem sourcePrincipalTorsion_iff_completionUnitLog_eq_zero
    (u : (CompletionIntegers v)ˣ) (hu : u ∈ sourcePrincipalUnits v) :
    u ∈ sourcePrincipalTorsion v ↔ completionUnitLog v u = 0 := by
  rw [mem_sourcePrincipalTorsion_iff]
  constructor
  · intro h
    exact (completionUnitLog_eq_zero_iff_isOfFinOrder v u).mpr h.1
  · intro h
    exact ⟨(completionUnitLog_eq_zero_iff_isOfFinOrder v u).mp h, hu⟩

/-- The principal torsion is the trace of the actual logarithm kernel on the
principal-unit subgroup. -/
theorem sourcePrincipalTorsion_eq_logKernel_inter :
    (sourcePrincipalTorsion v : Subgroup (CompletionIntegers v)ˣ) =
      (completionUnitLogHom v).ker ⊓ sourcePrincipalUnits v := by
  rw [completionUnitLogHom_ker_eq_torsion]
  rfl

/-- The actual principal torsion is a subgroup of the logarithm kernel. -/
theorem sourcePrincipalTorsion_le_logKernel :
    (sourcePrincipalTorsion v : Subgroup (CompletionIntegers v)ˣ) ≤
      (completionUnitLogHom v).ker :=
  by
  rw [sourcePrincipalTorsion_eq_logKernel_inter]
  exact inf_le_left

/-- Principal torsion maps to zero under the actual completion logarithm. -/
theorem completionUnitLog_eq_zero_of_sourcePrincipalTorsion
    {u : (CompletionIntegers v)ˣ} (hu : u ∈ sourcePrincipalTorsion v) :
    completionUnitLog v u = 0 :=
  MonoidHom.mem_ker.mp (sourcePrincipalTorsion_le_logKernel v hu)

/-- Every power of a principal torsion unit is again principal torsion. -/
theorem sourcePrincipalTorsion_pow_eq_one_of_mem
    {u : (CompletionIntegers v)ˣ} (hu : u ∈ sourcePrincipalTorsion v) :
    ∃ n : Nat, 0 < n ∧ u ^ n = 1 := by
  have hfin : IsOfFinOrder u := (mem_sourcePrincipalTorsion_iff v u).mp hu |>.1
  exact hfin.exists_pow_eq_one

/-- The normalized principal torsion projects to the actual principal torsion
through the actual completion unit equivalence. -/
noncomputable def normalizedPrincipalTorsionMap
    (u : CommGroup.torsion (Integers (NormalizedCompletion v))ˣ) :
    (CommGroup.torsion (CompletionIntegers v)ˣ :
      Subgroup (CompletionIntegers v)ˣ) :=
  ⟨normalizedCompletionUnitsEquiv v (u : (Integers (NormalizedCompletion v))ˣ), by
    rw [CommGroup.mem_torsion]
    exact MonoidHom.isOfFinOrder (normalizedCompletionUnitsEquiv v).toMonoidHom
      ((CommGroup.mem_torsion (u : (Integers (NormalizedCompletion v))ˣ)).mp u.property)⟩

theorem normalizedPrincipalTorsionMap_coe
    (u : CommGroup.torsion (Integers (NormalizedCompletion v))ˣ) :
    ((normalizedPrincipalTorsionMap v u :
        (CommGroup.torsion (CompletionIntegers v)ˣ :
          Subgroup (CompletionIntegers v)ˣ)) : (CompletionIntegers v)ˣ) =
      normalizedCompletionUnitsEquiv v (u : (Integers (NormalizedCompletion v))ˣ) :=
  rfl

/-- The torsion quotient logarithm is injective, hence principal torsion is
exactly the kernel of the quotient logarithm. -/
theorem completionUnitLogTorsionQuotientHom_injective_consumer :
    Function.Injective (completionUnitLogTorsionQuotientHom v) :=
  completionUnitLogTorsionQuotientHom_injective v

/-- A principal torsion unit is trivial in the torsion quotient. -/
theorem sourcePrincipalTorsion_quotient_eq_one
    {u : (CompletionIntegers v)ˣ} (hu : u ∈ sourcePrincipalTorsion v) :
    QuotientGroup.mk u =
      (1 : ((CompletionIntegers v)ˣ ⧸
        CommGroup.torsion (CompletionIntegers v)ˣ)) := by
  exact (QuotientGroup.eq_one_iff u).mpr (sourcePrincipalTorsion_le_torsion v hu)

/-- Normalized principal torsion: finite-order normalized principal units. -/
noncomputable def normalizedPrincipalTorsion :
    Subgroup (Integers (NormalizedCompletion v))ˣ :="
  (CommGroup.torsion (Integers (NormalizedCompletion v))ˣ :
      Subgroup (Integers (NormalizedCompletion v))ˣ) ⊓
    principalUnits (K := NormalizedCompletion v)

theorem mem_normalizedPrincipalTorsion_iff
    (u : (Integers (NormalizedCompletion v))ˣ) :
    u ∈ normalizedPrincipalTorsion v ↔
      IsOfFinOrder u ∧ u ∈ principalUnits (K := NormalizedCompletion v) := by
  rw [normalizedPrincipalTorsion, Subgroup.mem_inf]
  change IsOfFinOrder u ∧ u ∈ principalUnits (K := NormalizedCompletion v) ↔ _
  exact Iff.rfl

theorem normalizedPrincipalTorsion_le_principalUnits :
    (normalizedPrincipalTorsion v :
      Subgroup (Integers (NormalizedCompletion v))ˣ) ≤
      principalUnits (K := NormalizedCompletion v) :="
  inf_le_right

theorem normalizedPrincipalTorsion_le_torsion :
    (normalizedPrincipalTorsion v :
      Subgroup (Integers (NormalizedCompletion v))ˣ) ≤
      (CommGroup.torsion (Integers (NormalizedCompletion v))ˣ :
        Subgroup (Integers (NormalizedCompletion v))ˣ) :="
  inf_le_left

theorem normalizedPrincipalTorsion_one_mem :
    (1 : (Integers (NormalizedCompletion v))ˣ) ∈
      normalizedPrincipalTorsion v := by
  rw [mem_normalizedPrincipalTorsion_iff]
  exact ⟨IsOfFinOrder.one, (principalUnits (K := NormalizedCompletion v)).one_mem⟩

/-- On normalized principal units, finite order is exactly vanishing of the
normalized unit log. -/
theorem normalizedPrincipalTorsion_iff_unitLog_eq_zero
    (u : (Integers (NormalizedCompletion v))ˣ)
    (hu : u ∈ principalUnits (K := NormalizedCompletion v)) :
    u ∈ normalizedPrincipalTorsion v ↔
      unitLog (K := NormalizedCompletion v) u = 0 := by
  rw [mem_normalizedPrincipalTorsion_iff, hu, true_and]
  change IsOfFinOrder u ↔ unitLog (K := NormalizedCompletion v) u = 0
  exact (unitLog_eq_zero_iff_isOfFinOrder
    (p := (completionRationalPrime v).val) u).symm

/-- The source principal torsion is the intersection of the actual torsion
with the actual principal subgroup. -/
theorem sourcePrincipalTorsion_eq_inf :
    (sourcePrincipalTorsion v : Subgroup (CompletionIntegers v)ˣ) =
      (CommGroup.torsion (CompletionIntegers v)ˣ :
        Subgroup (CompletionIntegers v)ˣ) ⊓ sourcePrincipalUnits v :=
  rfl

/-- The normalized principal torsion is the intersection of the normalized
torsion with the normalized principal subgroup. -/
theorem normalizedPrincipalTorsion_eq_inf :
    (normalizedPrincipalTorsion v :
      Subgroup (Integers (NormalizedCompletion v))ˣ) =
      (CommGroup.torsion (Integers (NormalizedCompletion v))ˣ :
        Subgroup (Integers (NormalizedCompletion v))ˣ) ⊓
        principalUnits (K := NormalizedCompletion v) :="
  rfl

/-- The unit log is zero on normalized principal torsion. -/
theorem unitLog_eq_zero_of_normalizedPrincipalTorsion
    {u : (Integers (NormalizedCompletion v))ˣ}
    (hu : u ∈ normalizedPrincipalTorsion v) :
    unitLog (K := NormalizedCompletion v) u = 0 :=
  (normalizedPrincipalTorsion_iff_unitLog_eq_zero v u
    (normalizedPrincipalTorsion_le_principalUnits v hu)).mp hu

/-- A normalized principal torsion unit has a positive power equal to one. -/
theorem normalizedPrincipalTorsion_exists_pow_eq_one
    {u : (Integers (NormalizedCompletion v))ˣ}
    (hu : u ∈ normalizedPrincipalTorsion v) :
    ∃ n : Nat, 0 < n ∧ u ^ n = 1 :=
  ((mem_normalizedPrincipalTorsion_iff v u).mp hu).1.exists_pow_eq_one

/-- The source principal torsion is contained in the actual principal subgroup. -/
theorem sourcePrincipalTorsion_le_principal :
    (sourcePrincipalTorsion v : Subgroup (CompletionIntegers v)ˣ) ≤
      sourcePrincipalUnits v :=
  inf_le_right

/-- The actual principal torsion is contained in the actual unit torsion. -/
theorem sourcePrincipalTorsion_le_unitTorsion :
    (sourcePrincipalTorsion v : Subgroup (CompletionIntegers v)ˣ) ≤
      (CommGroup.torsion (CompletionIntegers v)ˣ :
        Subgroup (CompletionIntegers v)ˣ) :=
  inf_le_left

/-- The actual principal torsion is contained in the kernel of the completion
logarithm homomorphism. -/
theorem sourcePrincipalTorsion_le_logKernel_consumer :
    (sourcePrincipalTorsion v : Subgroup (CompletionIntegers v)ˣ) ≤
      (completionUnitLogHom v).ker :=
  sourcePrincipalTorsion_le_logKernel v

/-- Membership in the actual principal torsion is the conjunction of the
principal condition and finite order. -/
theorem sourcePrincipalTorsion_mem_iff_principal_and_finite
    (u : (CompletionIntegers v)ˣ) :
    u ∈ sourcePrincipalTorsion v ↔
      u ∈ sourcePrincipalUnits v ∧ IsOfFinOrder u := by
  rw [mem_sourcePrincipalTorsion_iff]
  exact and_comm

/-- The actual principal torsion is a subgroup of the actual principal units. -/
theorem sourcePrincipalTorsion_subgroup_principal :
    (sourcePrincipalTorsion v : Subgroup (CompletionIntegers v)ˣ) =
      (CommGroup.torsion (CompletionIntegers v)ˣ :
        Subgroup (CompletionIntegers v)ˣ) ⊓ sourcePrincipalUnits v :=
  rfl

/-- The normalized principal torsion is closed under inverses. -/
theorem normalizedPrincipalTorsion_inv_mem
    {u : (Integers (NormalizedCompletion v))ˣ}
    (hu : u ∈ normalizedPrincipalTorsion v) :
    u⁻¹ ∈ normalizedPrincipalTorsion v := by
  rw [mem_normalizedPrincipalTorsion_iff] at hu ⊢
  exact ⟨hu.1.inv, (principalUnits (K := NormalizedCompletion v)).inv_mem hu.2⟩

/-- The normalized principal torsion is closed under multiplication. -/
theorem normalizedPrincipalTorsion_mul_mem
    {u w : (Integers (NormalizedCompletion v))ˣ}
    (hu : u ∈ normalizedPrincipalTorsion v)
    (hw : w ∈ normalizedPrincipalTorsion v) :
    u * w ∈ normalizedPrincipalTorsion v := by
  rw [mem_normalizedPrincipalTorsion_iff] at hu hw ⊢
  exact ⟨hu.1.mul hw.1, (principalUnits (K := NormalizedCompletion v)).mul_mem hu.2 hw.2⟩

/-- The normalized principal torsion is closed under powers. -/
theorem normalizedPrincipalTorsion_pow_mem
    {u : (Integers (NormalizedCompletion v))ˣ}
    (hu : u ∈ normalizedPrincipalTorsion v) (n : Nat) :
    u ^ n ∈ normalizedPrincipalTorsion v := by
  rw [mem_normalizedPrincipalTorsion_iff] at hu ⊢
  exact ⟨hu.1.pow (n := n), (principalUnits (K := NormalizedCompletion v)).pow_mem hu.2 n⟩

/-- The normalized principal torsion maps into the actual principal torsion
along the actual unit equivalence, after taking the inverse image. -/
theorem normalizedPrincipalTorsion_transport_mem
    {u : (Integers (NormalizedCompletion v))ˣ}
    (hu : u ∈ normalizedPrincipalTorsion v)
    (hprincipal : normalizedCompletionUnitsEquiv v u ∈ sourcePrincipalUnits v) :
    normalizedCompletionUnitsEquiv v u ∈ sourcePrincipalTorsion v := by
  rw [mem_sourcePrincipalTorsion_iff]
  refine ⟨?_, hprincipal⟩
  exact (mem_normalizedPrincipalTorsion_iff v u).mp hu |>.1.map
    (normalizedCompletionUnitsEquiv v).toMonoidHom

/-- The actual principal torsion and the normalized principal torsion have the
same unit-log kernel condition after transport. -/
theorem sourcePrincipalTorsion_uniform_kernel :
    (sourcePrincipalTorsion v : Subgroup (CompletionIntegers v)ˣ) ≤
      (completionUnitLogHom v).ker :=
  sourcePrincipalTorsion_le_logKernel v

/-- The actual principal torsion is nonempty. -/
theorem sourcePrincipalTorsion_nonempty :
    (sourcePrincipalTorsion v : Set (CompletionIntegers v)ˣ).Nonempty :=
  ⟨1, sourcePrincipalTorsion_one_mem v⟩

/-- The normalized principal torsion is nonempty. -/
theorem normalizedPrincipalTorsion_nonempty :
    (normalizedPrincipalTorsion v :
      Set (Integers (NormalizedCompletion v))ˣ).Nonempty :=
  ⟨1, normalizedPrincipalTorsion_one_mem v⟩

/-- Every element of the actual principal torsion has finite order. -/
theorem sourcePrincipalTorsion_isOfFinOrder
    {u : (CompletionIntegers v)ˣ} (hu : u ∈ sourcePrincipalTorsion v) :
    IsOfFinOrder u :=
  (mem_sourcePrincipalTorsion_iff v u).mp hu |>.1

/-- Every element of the normalized principal torsion has finite order. -/
theorem normalizedPrincipalTorsion_isOfFinOrder
    {u : (Integers (NormalizedCompletion v))ˣ}
    (hu : u ∈ normalizedPrincipalTorsion v) :
    IsOfFinOrder u :=
  (mem_normalizedPrincipalTorsion_iff v u).mp hu |>.1

/-- The actual principal torsion is stable under inverse. -/
theorem sourcePrincipalTorsion_inv_iff
    (u : (CompletionIntegers v)ˣ) :
    u⁻¹ ∈ sourcePrincipalTorsion v ↔ u ∈ sourcePrincipalTorsion v := by
  constructor
  · intro h
    have h' : (u⁻¹)⁻¹ ∈ sourcePrincipalTorsion v :=
      sourcePrincipalTorsion_inv_mem h
    simpa using h'
  · exact sourcePrincipalTorsion_inv_mem

/-- The normalized principal torsion is stable under inverse. -/
theorem normalizedPrincipalTorsion_inv_iff
    (u : (Integers (NormalizedCompletion v))ˣ) :
    u⁻¹ ∈ normalizedPrincipalTorsion v ↔
      u ∈ normalizedPrincipalTorsion v := by
  constructor
  · intro h
    have h' : (u⁻¹)⁻¹ ∈ normalizedPrincipalTorsion v :=
      normalizedPrincipalTorsion_inv_mem h
    simpa using h'
  · exact normalizedPrincipalTorsion_inv_mem

/-- The actual principal torsion is contained in the actual principal-unit
subgroup, in intersection form. -/
theorem sourcePrincipalTorsion_eq_torsion_inf :
    (sourcePrincipalTorsion v : Subgroup (CompletionIntegers v)ˣ) =
      (CommGroup.torsion (CompletionIntegers v)ˣ :
        Subgroup (CompletionIntegers v)ˣ) ⊓ sourcePrincipalUnits v :=
  rfl

/-- The normalized principal torsion is contained in the normalized principal
subgroup. -/
theorem normalizedPrincipalTorsion_le_principal :
    (normalizedPrincipalTorsion v :
      Subgroup (Integers (NormalizedCompletion v))ˣ) ≤
      principalUnits (K := NormalizedCompletion v) :="
  inf_le_right

/-- The unit log vanishes on every normalized principal torsion element. -/
theorem unitLog_eq_zero_of_mem_normalizedPrincipalTorsion
    {u : (Integers (NormalizedCompletion v))ˣ}
    (hu : u ∈ normalizedPrincipalTorsion v) :
    unitLog (K := NormalizedCompletion v) u = 0 :=
  unitLog_eq_zero_of_normalizedPrincipalTorsion v hu

/-- The completion logarithm vanishes on every actual principal torsion
element. -/
theorem completionUnitLog_eq_zero_of_mem_sourcePrincipalTorsion
    {u : (CompletionIntegers v)ˣ} (hu : u ∈ sourcePrincipalTorsion v) :
    completionUnitLog v u = 0 :=
  completionUnitLog_eq_zero_of_sourcePrincipalTorsion v hu

end LeanFormal.IUT.PrincipalUnitTorsionConsumer
