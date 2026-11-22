/- R5 step 3 (elementwise B-version): differentIdeal Z_p (Integers Q_p) = top.

traceDual at B = Integers Q_p: I = unit submodule of B over L = FractionRing B.
Reuse: Submodule.mem_traceDual / Algebra.trace_self_apply / Submodule.one_mem_div.
-/
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.NumberTheory.Padics.PadicIntegers
import LeanFormal.IUT.Foundations.LocalFields.IntegralTraceDualTensorInclusion
import tmp.sheaf.xif.paper.Mzk1G1LocalDifferentOrderZeroActual
import Mathlib.Tactic
noncomputable section
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
namespace LeanFormal.IUT.XiFPaper.Mzk1G1BaseDifferentTransportActual

open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.IntegralTraceDualTensorInclusion
open LeanFormal.IUT.LocalDifferentUpperBound
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.Mzk1G1LocalDifferentOrderZeroActual

variable {p : Nat} [Fact p.Prime]
local instance : IsDedekindDomain (Integers ℚ_[p]) :=
  integersIsDedekindDomain (p := p) (L := ℚ_[p])
local instance : IsScalarTower ℤ_[p] (Integers ℚ_[p]) (FractionRing ℚ_[p]) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/-- traceDual of the unit submodule for B = Integers Q_p is contained in the unit submodule. -/
theorem traceDual_one_le_one_rat :
    Submodule.traceDual ℤ_[p] (FractionRing (Integers ℚ_[p]))
        (1 : Submodule (Integers ℚ_[p]) (FractionRing (Integers ℚ_[p]))) ≤ 1 := by
  intro y hy
  rw [Submodule.mem_one]
  have hy1 :=
    (Submodule.mem_traceDual (A := ℤ_[p]) (K := FractionRing (Integers ℚ_[p]))
      (L := FractionRing (Integers ℚ_[p])) (B := Integers ℚ_[p])
      (I := (1 : Submodule (Integers ℚ_[p]) (FractionRing (Integers ℚ_[p]))))).mp hy 1
      (Submodule.mem_one.mpr ⟨1, by simp⟩)
  rw [Algebra.traceForm_apply, mul_one, Algebra.trace_self_apply] at hy1
  rcases RingHom.mem_range.mp hy1 with ⟨a, ha⟩
  refine ⟨⟨(a : ℚ_[p]), ?_⟩, ?_⟩
  · exact PadicInt.norm_le_one a
  · simpa using ha

/-- The base different ideal of Integers Q_p over Z_p is top. -/
theorem differentIdeal_integersRat_eq_top :
    differentIdeal ℤ_[p] (Integers ℚ_[p]) = ⊤ := by
  rw [Ideal.eq_top_iff_one, differentIdeal, Submodule.mem_comap]
  change algebraMap ℤ_[p] (FractionRing ℚ_[p]) 1 ∈
    (1 : Submodule (Integers ℚ_[p]) (FractionRing ℚ_[p])) /
      Submodule.traceDual ℤ_[p] (FractionRing ℚ_[p])
        (1 : Submodule (Integers ℚ_[p]) (FractionRing ℚ_[p]))
  rw [map_one, Submodule.one_mem_div]
  exact traceDual_one_le_one_rat

/-- Base paper order vanishes. -/
theorem localDifferentPaperOrder_rat_eq_zero' :
    localDifferentPaperOrder (p := p) (L := ℚ_[p]) = 0 := by
  refine localDifferentPaperOrder_eq_zero_of_localDifferentIdeal_eq_top (p := p) (L := ℚ_[p]) ?_
  simpa [localDifferentIdeal] using differentIdeal_integersRat_eq_top (p := p)

#print axioms differentIdeal_integersRat_eq_top
#print axioms localDifferentPaperOrder_rat_eq_zero'
end LeanFormal.IUT.XiFPaper.Mzk1G1BaseDifferentTransportActual
