/- Route 7.2, paperOrder base case: the relative different of Z_p inside the Integers of Q_p is
the unit ideal, hence the base paperOrder vanishes. -/
import tmp.sheaf.xif.paper.Mzk1G1PadicLocalDonorActual
import tmp.sheaf.xif.paper.Mzk1G1LocalDifferentOrderZeroActual
import LeanFormal.IUT.Foundations.LocalFields.LocalDifferentUpperBound
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.Tactic
noncomputable section
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PaperOrderBaseActual

open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.IntegralTraceDualTensorInclusion
open LeanFormal.IUT.XiFPaper.Mzk1G1LocalDifferentOrderZeroActual
open Submodule

variable {p : Nat} [Fact p.Prime]

local instance : IsIntegrallyClosed ℤ_[p] := padicInt_isIntegrallyClosed (p := p)
local instance : IsDedekindDomain ℤ_[p] := by infer_instance
local instance : IsDedekindDomain (Integers ℚ_[p]) :=
  integersIsDedekindDomain (p := p) (L := ℚ_[p])
local instance : Module.IsTorsionFree ℤ_[p] (Integers ℚ_[p]) :=
  integersIsTorsionFree (p := p) (L := ℚ_[p])
local instance : IsScalarTower ℤ_[p] (Integers ℚ_[p]) ℚ_[p] :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)
local instance : IsScalarTower ℤ_[p] ℚ_[p] ℚ_[p] :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/-- The trace dual of the unit submodule in the self-extension Q_p/Z_p is the unit submodule. -/
theorem traceDual_rat_one_eq_one :
    Submodule.traceDual ℤ_[p] ℚ_[p] (1 : Submodule (Integers ℚ_[p]) ℚ_[p]) = 1 := by
  apply le_antisymm
  · intro x hx
    rw [Submodule.mem_one]
    have hx' := (Submodule.mem_traceDual (A := ℤ_[p]) (K := ℚ_[p]) (L := ℚ_[p])
      (B := Integers ℚ_[p]) (I := (1 : Submodule (Integers ℚ_[p]) ℚ_[p]))).mp hx 1
      (Submodule.mem_one.mpr ⟨1, map_one (algebraMap (Integers ℚ_[p]) ℚ_[p])⟩)
    rw [Algebra.traceForm_apply, mul_one, Algebra.trace_self_apply] at hx'
    exact hx'
  · intro x hx
    rw [Submodule.mem_one] at hx
    obtain ⟨b, rfl⟩ := hx
    rw [Submodule.mem_traceDual]
    intro a ha
    rw [Submodule.mem_one] at ha
    obtain ⟨c, rfl⟩ := ha
    rw [Algebra.traceForm_apply, Algebra.trace_self_apply, ← map_mul]
    exact ⟨⟨((b * c : Integers ℚ_[p]) : ℚ_[p]), (b * c).property⟩, rfl⟩

/-- The trace dual of the unit submodule in the self-extension Q_p/Z_p, transported to the
canonical FractionRing types used by differentIdeal. -/
theorem traceDual_rat_one_eq_one' :
    Submodule.traceDual ℤ_[p] (FractionRing ℤ_[p])
      (1 : Submodule (Integers ℚ_[p]) (FractionRing (Integers ℚ_[p]))) = 1 := by
  let e : FractionRing (Integers ℚ_[p]) ≃ₐ[Integers ℚ_[p]] ℚ_[p] :=
    FractionRing.algEquiv (Integers ℚ_[p]) ℚ_[p]
  have hone : (1 : Submodule (Integers ℚ_[p]) (FractionRing (Integers ℚ_[p]))).map
      e.toLinearMap = 1 := by
    rw [Submodule.one_eq_span_one_set, Submodule.map_span]
    simp [Set.image_singleton]
  have hmap := Submodule.map_equiv_traceDual (A := ℤ_[p]) (K := ℚ_[p])
    (B := Integers ℚ_[p]) (L := ℚ_[p])
    (1 : Submodule (Integers ℚ_[p]) (FractionRing (Integers ℚ_[p])))
  rw [hone, traceDual_rat_one_eq_one] at hmap
  exact Submodule.map_injective_of_injective (f := e.toLinearMap) e.injective
    (by rw [hmap, hone])

/-- The relative different of Z_p in the integers of Q_p is the unit ideal. -/
theorem differentIdeal_rat_self_top : differentIdeal ℤ_[p] (Integers ℚ_[p]) = ⊤ := by
  rw [Ideal.eq_top_iff_one, differentIdeal, Submodule.mem_comap, map_one,
    traceDual_rat_one_eq_one', Submodule.one_mem_div]
  exact le_rfl

/-- The base paperOrder at Q_p vanishes. -/
theorem localDifferentPaperOrder_rat_eq_zero :
    localDifferentPaperOrder (p := p) (L := ℚ_[p]) = 0 := by
  apply localDifferentPaperOrder_eq_zero_of_localDifferentIdeal_eq_top
  show localDifferentIdeal (p := p) (L := ℚ_[p]) = ⊤
  show differentIdeal ℤ_[p] (Integers ℚ_[p]) = ⊤
  exact differentIdeal_rat_self_top

#print axioms traceDual_rat_one_eq_one'
#print axioms differentIdeal_rat_self_top
#print axioms localDifferentPaperOrder_rat_eq_zero
end LeanFormal.IUT.XiFPaper.Mzk1G1PaperOrderBaseActual
