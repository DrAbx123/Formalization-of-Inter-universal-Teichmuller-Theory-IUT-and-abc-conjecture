import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import tmp.sheaf.xif.paper.Mzk1G1KvCompactActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.G1LocalHeightCriterionActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.G1KvCompactActual

universe u

/-- The normalized discriminant D(K) = log |disc K| / [K : Q] of a number
field, written with natAbs (which is |disc K|).  This is the actual object
appearing in route section 6.1 (D1). -/
noncomputable def discOver (K : Type*) [Field K] [NumberField K] : ℝ :=
  Real.log ((NumberField.discr K).natAbs : ℝ) / (Module.finrank ℚ K : ℝ)

/-- A finite place is bad for lam when lam meets the divisor
(0) + (1) + (infinity) there, i.e. when lam reduces to 0, 1 or infinity. -/
def IsBadPlace {K : Type*} [Field K] [NumberField K] (lam : K)
    (v : NumberField.FinitePlace K) : Prop :=
  v lam ≠ 1 ∨ v (lam - 1) ≠ 1

/-- The normalized truncated conductor N_{0,1,infinity}(lam): at every bad
finite place we count the residue degree log Nv once (truncated exponent), and
normalize by [K : Q].  For a fixed rational prime p the total normalized
contribution is at most log p, exactly as used in route section 6.1 and 8.2. -/
noncomputable def truncConductor {K : Type*} [Field K] [NumberField K]
    (lam : K) : ℝ := by
  classical
  exact (∑ᶠ v : NumberField.FinitePlace K,
      if IsBadPlace lam v then
        Real.log (max 1 (((Ideal.absNorm
          (NumberField.FinitePlace.maximalIdeal v).asIdeal : ℕ)) : ℝ))
      else 0) /
    (Module.finrank ℚ K : ℝ)

/-- The discriminant term is nonnegative: |disc K| >= 1 for every number
field. -/
theorem discOver_nonneg (K : Type*) [Field K] [NumberField K] :
    0 ≤ discOver K := by
  unfold discOver
  apply div_nonneg
  · apply Real.log_nonneg
    have hz : NumberField.discr K ≠ 0 := NumberField.discr_ne_zero K
    have hpos : 0 < (NumberField.discr K).natAbs := Int.natAbs_pos.mpr hz
    exact_mod_cast hpos
  · exact Nat.cast_nonneg _

/-- The truncated conductor is nonnegative. -/
theorem truncConductor_nonneg {K : Type*} [Field K] [NumberField K]
    (lam : K) : 0 ≤ truncConductor lam := by
  unfold truncConductor
  apply div_nonneg
  · apply finsum_nonneg
    intro v
    split_ifs with hbad
    · exact Real.log_nonneg (le_max_left 1 _)
    · exact le_rfl
  · exact Nat.cast_nonneg _

/-- The actual local height criterion D1 of route section 6.1: for a fixed
degree bound d, a fixed actual compact local domain K_V and a fixed eta > 0
there is a constant C such that every element lam of a number field K of degree
at most d whose all local conjugates lie in K_V satisfies
h(lam) <= (1 + eta) * (D(K) + N_{0,1,infinity}(lam)) + C. -/
def LocalHeightCriterion (d : ℕ) (D : KvData) (η : ℝ) : Prop :=
  ∃ C : ℝ, ∀ (K : Type u) [Field K] [NumberField K],
    Module.finrank ℚ K ≤ d → ∀ lam : K, InKv D lam →
      Height.logHeight₁ lam ≤
        (1 + η) * (discOver K + truncConductor lam) + C

/-- The full quantifier form of D1 in the route: for every degree bound d,
every actual compact local domain K_V and every eta > 0 there is C. -/
def ActualD1 : Prop :=
  ∀ (d : ℕ) (D : KvData) (η : ℝ), 0 < η → LocalHeightCriterion.{u} d D η

/-- The route quantifier form is exactly the family of criteria. -/
theorem actualD1_iff :
    ActualD1.{u} ↔ ∀ (d : ℕ) (D : KvData) (η : ℝ), 0 < η →
      LocalHeightCriterion.{u} d D η :=
  Iff.rfl

/-- A D1 consumer: the criterion unpacked as an existential bound. -/
theorem localHeightCriterion_bound {d : ℕ} {D : KvData} {η : ℝ}
    (h : LocalHeightCriterion.{u} d D η) :
    ∃ C : ℝ, ∀ (K : Type u) [Field K] [NumberField K],
      Module.finrank ℚ K ≤ d → ∀ lam : K, InKv D lam →
        Height.logHeight₁ lam ≤
          (1 + η) * (discOver K + truncConductor lam) + C :=
  h

#print axioms discOver_nonneg
#print axioms truncConductor_nonneg
#print axioms actualD1_iff

end LeanFormal.IUT.XiFPaper.G1LocalHeightCriterionActual
end
