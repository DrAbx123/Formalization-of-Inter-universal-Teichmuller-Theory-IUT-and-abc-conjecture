/- Route 7.2 base case: different ideal of Z_p over itself is top (retry 2, specialized).

Reuse / 查重: same statement in LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceHolomorphicDifferentBase.lean
(RED, traceDual instance mismatch); here the generic lemma is specialized to A = Z_p so the
FractionRing algebra instance is unambiguous.
-/
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.NumberTheory.Padics.PadicIntegers
import LeanFormal.IUT.Foundations.LocalFields.IntegralTraceDualTensorInclusion
import LeanFormal.IUT.Foundations.LocalFields.LocalDifferentUpperBound
import tmp.sheaf.xif.paper.Mzk1G1LocalDifferentOrderZeroActual
import Mathlib.Tactic
noncomputable section
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.IntegralTraceDualTensorInclusion
open LeanFormal.IUT.LocalDifferentUpperBound
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.Mzk1G1LocalDifferentOrderZeroActual
namespace LeanFormal.IUT.XiFPaper.Mzk1G1BaseDifferentTopActual

/-- In a self-extension, the trace dual of the unit submodule is contained in the unit submodule. -/
theorem traceDual_one_le_one_self' {A K : Type*} [CommRing A] [Field K] [Algebra A K] :
    Submodule.traceDual A K (1 : Submodule A K) ≤ 1 := by
  intro x hx
  rw [Submodule.mem_one]
  have hx' :=
    (Submodule.mem_traceDual (A := A) (K := K) (L := K) (B := A)
      (I := (1 : Submodule A K))).mp hx 1
      (Submodule.mem_one.mpr ⟨1, map_one (algebraMap A K)⟩)
  rw [Algebra.traceForm_apply, mul_one, Algebra.trace_self_apply] at hx'
  exact hx'

/-- Specialized to Z_p: the self-different is top. -/
theorem differentIdeal_padicInt_self_eq_top' (p : Nat) [Fact p.Prime] :
    differentIdeal ℤ_[p] ℤ_[p] = ⊤ := by
  rw [Ideal.eq_top_iff_one, differentIdeal, Submodule.mem_comap]
  change algebraMap ℤ_[p] (FractionRing ℤ_[p]) 1 ∈
    (1 : Submodule ℤ_[p] (FractionRing ℤ_[p])) /
      Submodule.traceDual ℤ_[p] (FractionRing ℤ_[p]) 1
  rw [map_one, Submodule.one_mem_div]
  exact traceDual_one_le_one_self' (A := ℤ_[p]) (K := FractionRing ℤ_[p])

/-- The base different ideal of Q_p over Z_p is top (Integers Q_p is Z_p definitionally). -/
theorem differentIdeal_rat_self_top' (p : Nat) [Fact p.Prime]
    [IsDedekindDomain (Integers ℚ_[p])] :
    differentIdeal ℤ_[p] (Integers ℚ_[p]) = ⊤ := by
  simpa [LeanFormal.IUT.LocalFieldIntegralUnits.Integers]
    using differentIdeal_padicInt_self_eq_top' p

/-- Base paper order vanishes. -/
theorem localDifferentPaperOrder_rat_eq_zero' (p : Nat) [Fact p.Prime]
    [IsDedekindDomain (Integers ℚ_[p])] :
    localDifferentPaperOrder (p := p) (L := ℚ_[p]) = 0 := by
  refine localDifferentPaperOrder_eq_zero_of_localDifferentIdeal_eq_top (p := p) (L := ℚ_[p]) ?_
  simpa [localDifferentIdeal] using differentIdeal_rat_self_top' p

#print axioms differentIdeal_padicInt_self_eq_top'
#print axioms localDifferentPaperOrder_rat_eq_zero'
end LeanFormal.IUT.XiFPaper.Mzk1G1BaseDifferentTopActual
