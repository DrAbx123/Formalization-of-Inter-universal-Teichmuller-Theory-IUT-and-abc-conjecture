import LeanFormal.IUT.IUTII.Frobenioid.Example36EllipticCurveTateHigherLevel
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# All 2-power torsion levels and the inverse system of finite groups

For the concrete curve `y^2 = x^3 - x` over the separable closure of `Q` this
file generalizes the level-2/level-4 torsion construction of
`Example36EllipticCurveTateHigherLevel` to all 2-power levels:

* `tatePowerTwoLevel n` is the actual subgroup `E[2^n] = {P | 2^n • P = 0}`;
* `tatePowerTwoTransition n : E[2^{n+1}] -> E[2^n]` is multiplication by `2`,
  proved additive; two successive transitions compose to multiplication by
  `4`;
* the kernel of the transition is the 2-torsion subgroup `E[2]` (finite, the
  four explicit points); the range is a subgroup of the lower finite level, so
  induction using `finite_of_finite_ker_of_finite_range` proves finiteness of
  every `E[2^n]`; the level `n = 0` of `E[2^n]` is trivial (`E[1] = 0`).

Thus `(E[2^n], [2])` is a genuine inverse system of finite groups.  The actual
inverse limit below is indexed by `n >= 0` as `E[2^(n+1)]`, so that the trivial
level `E[1]` is omitted and every level of the system is `E[2^(n+1)]`.

The finite discrete groups `E[2^(n+1)]` (`n >= 0`, so level 0 is `E[2]`; the
trivial level `E[1] = 0` is omitted) together with the transitions `[2]` form an
`N^op` diagram in `ProfiniteGrp`; its actual general limit
`tatePowerTwoProfiniteLimit` is constructed with Mathlib's general small-diagram
limits (`ProfiniteGrp.limit`, `ProfiniteGrp.limitCone`,
`ProfiniteGrp.limitConeIsLimit`), with actual projections, compatibility and the
universal property.  General limits in `ProfiniteGrp` exist for every small
diagram (ProfiniteGrp/Basic.lean:312-371); therefore no surjectivity of the
transitions and no Krull continuity of a Galois action is needed for the limit
object or its universal property.

The following additional properties are NOT needed to form the limit and are
kept as separate frozen cards:
* `tatePowerTwoTransitionSurjectiveCard`: surjectivity of the level
  transitions, needed for the projective-limit quotient property
  `T_2/l^n T_2 = E[2^n]` (not for the limit itself);
* `tatePowerTwoGaloisContinuityCard`: Krull-continuity of the Galois action on
  a finite torsion level (not needed for the abstract limit);
* `oddTorsionFinitenessCard`: the general odd-`l` torsion finiteness and
  level-transition criterion.

Boundary: finite 2-power torsion of the concrete curve and its actual pro-2
inverse limit only; the limit is not endowed with a Galois action, and no
continuous Galois representation, no nonabelian curve fundamental group and no
theta/q-pilot claim are made.
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open CategoryTheory WeierstrassCurve

/-- The geometric point type of the concrete curve `y^2 = x^3 - x`. -/
abbrev tateAllLevelsPointType := tateLevelFourPointType

local instance instDecidableEqTateGeometricBaseTorsionLevels :
    DecidableEq tateGeometricBase :=
  Classical.decEq tateGeometricBase

/-- The `2^n`-torsion subgroup `E[2^n] = {P | (2^n) P = 0}`. -/
noncomputable abbrev tatePowerTwoLevel (n : ℕ) : AddSubgroup tateAllLevelsPointType :=
  LeanFormal.IUT.ABCBridge.Galois.torsionSubgroup
    (curveY2EqX3SubX⁄tateGeometricBase) (2 ^ n)

theorem tatePowerTwoLevel_mem_iff (n : ℕ) {P : tateAllLevelsPointType} :
    P ∈ tatePowerTwoLevel n ↔ (2 ^ n : ℕ) • P = 0 :=
  LeanFormal.IUT.ABCBridge.Galois.mem_torsionSubgroup

/-- The level transition `E[2^{n+1}] -> E[2^n]`, multiplication by two. -/
noncomputable def tatePowerTwoTransition (n : ℕ) :
    tatePowerTwoLevel (n + 1) →+ tatePowerTwoLevel n where
  toFun P := ⟨(2 : ℕ) • P.1, by
    rw [tatePowerTwoLevel_mem_iff]
    have hP : (2 ^ (n + 1) : ℕ) • P.1 = 0 :=
      (tatePowerTwoLevel_mem_iff (n + 1)).mp P.2
    rw [pow_succ, mul_comm, mul_nsmul] at hP
    exact hP⟩
  map_zero' := Subtype.ext (by simp)
  map_add' P Q := Subtype.ext (by
    simp only [AddSubgroup.coe_add, two_nsmul]
    abel)

/-- The level transition is additive. -/
theorem tatePowerTwoTransition_add (n : ℕ) (P Q : tatePowerTwoLevel (n + 1)) :
    tatePowerTwoTransition n (P + Q) =
      tatePowerTwoTransition n P + tatePowerTwoTransition n Q :=
  (tatePowerTwoTransition n).map_add P Q

/-- The level-`0` torsion is trivial: `E[1] = {0}`. -/
theorem tatePowerTwoLevel_zero_eq_bot : tatePowerTwoLevel 0 = ⊥ := by
  ext P
  rw [tatePowerTwoLevel_mem_iff, AddSubgroup.mem_bot]
  constructor
  · intro h
    simpa using h
  · intro h
    subst h
    simp

/-- The kernel of `E[2^{n+1}] -> E[2^n]` is the 2-torsion subgroup. -/
noncomputable def tatePowerTwoKernelEquiv (n : ℕ) :
    (tatePowerTwoTransition n).ker ≃+ tateLevelTwoTorsion where
  toFun x := ⟨x.1.1, by
    have hx : tatePowerTwoTransition n x.1 = 0 := x.2
    have h2 : (2 : ℕ) • x.1.1 = 0 := congrArg Subtype.val hx
    exact tateLevelTwo_mem_iff.mpr h2⟩
  invFun Q := ⟨⟨Q.1, by
    rw [tatePowerTwoLevel_mem_iff]
    have h2 : (2 : ℕ) • Q.1 = 0 := tateLevelTwo_mem_iff.mp Q.2
    rw [pow_succ, mul_comm, mul_nsmul, h2, nsmul_zero]⟩, by
    apply Subtype.ext
    exact tateLevelTwo_mem_iff.mp Q.2⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv Q := by
    apply Subtype.ext
    rfl
  map_add' x y := rfl

theorem tatePowerTwoKernel_finite (n : ℕ) : Finite (tatePowerTwoTransition n).ker :=
  Finite.of_injective (tatePowerTwoKernelEquiv n).toFun (tatePowerTwoKernelEquiv n).injective

/-- The zero level `E[1] = {0}` is finite. -/
theorem tatePowerTwoLevel_zero_finite : Finite (tatePowerTwoLevel 0) := by
  refine Finite.of_injective
    (fun _ : tatePowerTwoLevel 0 => ()) ?_
  intro a b _
  apply Subtype.ext
  rw [AddSubgroup.mem_bot.mp ((tatePowerTwoLevel_zero_eq_bot).le a.2),
    AddSubgroup.mem_bot.mp ((tatePowerTwoLevel_zero_eq_bot).le b.2)]

/-- **Every 2-power torsion level is finite.** -/
theorem tatePowerTwoLevel_finite (n : ℕ) : Finite (tatePowerTwoLevel n) := by
  induction n with
  | zero => exact tatePowerTwoLevel_zero_finite
  | succ n ih =>
      haveI : Finite (tatePowerTwoLevel n) := ih
      have hrange : Finite (tatePowerTwoTransition n).range :=
        Finite.of_injective
          (fun x : (tatePowerTwoTransition n).range => (x.1 : tatePowerTwoLevel n))
          Subtype.val_injective
      exact finite_of_finite_ker_of_finite_range (tatePowerTwoTransition n)
        (tatePowerTwoKernel_finite n) hrange

noncomputable instance tatePowerTwoLevelFinite (n : ℕ) : Finite (tatePowerTwoLevel n) :=
  tatePowerTwoLevel_finite n

/-- **Two successive transitions compose to multiplication by `4`.** -/
theorem tatePowerTwoTransition_comp_apply (n : ℕ) (P : tatePowerTwoLevel (n + 2)) :
    (tatePowerTwoTransition n (tatePowerTwoTransition (n + 1) P) :
        tateAllLevelsPointType) = (4 : ℕ) • P.1 := by
  show (tatePowerTwoTransition n (tatePowerTwoTransition (n + 1) P)).1 =
    (4 : ℕ) • P.1
  change (2 : ℕ) • ((tatePowerTwoTransition (n + 1) P).1) = (4 : ℕ) • P.1
  change (2 : ℕ) • ((2 : ℕ) • P.1) = (4 : ℕ) • P.1
  rw [← mul_nsmul]

/-- **The genuine inverse system of finite 2-power torsion groups.** -/
theorem tatePowerTwoLevel_genuine_inverseSystem :
    (∀ n, Finite (tatePowerTwoLevel n)) ∧
      (tatePowerTwoLevel 0 = ⊥) ∧
      (∀ (n : ℕ) (P : tatePowerTwoLevel (n + 2)),
        (tatePowerTwoTransition n (tatePowerTwoTransition (n + 1) P) :
            tateAllLevelsPointType) = (4 : ℕ) • P.1) :=
  ⟨tatePowerTwoLevel_finite, tatePowerTwoLevel_zero_eq_bot,
    tatePowerTwoTransition_comp_apply⟩

/-! ## The actual N^op inverse system and its general limit -/

/-- The finite discrete profinite group of the actual level `E[2^(n+1)]`.
Level `n = 0` is `E[2]`, not the trivial `E[1]`, so every level of this inverse
system is a 2-power torsion level with exponent at least one. -/
noncomputable def tatePowerTwoProfiniteTateLevel (n : ℕ) : ProfiniteGrp :=
  ProfiniteGrp.ofFiniteGrp
    (FiniteGrp.of (Multiplicative (tatePowerTwoLevel (n + 1))))

/-- The transition `[2] : E[2^(n+2)] -> E[2^(n+1)]` as a morphism of finite
discrete profinite groups. -/
noncomputable def tatePowerTwoProfiniteTransition (n : ℕ) :
    tatePowerTwoProfiniteTateLevel (n + 1) ⟶ tatePowerTwoProfiniteTateLevel n :=
  ProfiniteGrp.ofFiniteGrpHom
    (FiniteGrp.ofHom (AddMonoidHom.toMultiplicative (tatePowerTwoTransition (n + 1))))

/-- **The actual N^op inverse system of the finite 2-power torsion levels.**
Organized over `N^op` with Mathlib `Functor.ofOpSequence`; no transition
surjectivity and no Krull continuity is used to form the diagram. -/
noncomputable def tatePowerTwoProfiniteDiagram : ℕᵒᵖ ⥤ ProfiniteGrp :=
  Functor.ofOpSequence tatePowerTwoProfiniteTransition

/-- **The actual general limit of the 2-power torsion inverse system.**  This is
the pro-2 inverse limit `lim_n E[2^(n+1)]`, constructed with Mathlib's general
small-diagram limits in `ProfiniteGrp` (`ProfiniteGrp.limit`). -/
noncomputable def tatePowerTwoProfiniteLimit : ProfiniteGrp :=
  (ProfiniteGrp.limitCone tatePowerTwoProfiniteDiagram).pt

/-- The actual projection from the limit to the finite level `E[2^(n+1)]`. -/
noncomputable def tatePowerTwoProfiniteLimitProjection (n : ℕ) :
    tatePowerTwoProfiniteLimit ⟶ tatePowerTwoProfiniteTateLevel n :=
  (ProfiniteGrp.limitCone tatePowerTwoProfiniteDiagram).π.app ⟨n⟩

/-- The projections are compatible with the transition maps. -/
theorem tatePowerTwoProfiniteLimitProjection_compatible (n : ℕ) :
    tatePowerTwoProfiniteLimitProjection (n + 1) ≫ tatePowerTwoProfiniteTransition n =
      tatePowerTwoProfiniteLimitProjection n :=
  by
    have hmap : tatePowerTwoProfiniteDiagram.map (homOfLE (Nat.le_add_right n 1)).op =
        tatePowerTwoProfiniteTransition n := by
      exact (Functor.ofOpSequence_map_homOfLE_succ tatePowerTwoProfiniteTransition n)
    have hnat := ((ProfiniteGrp.limitCone tatePowerTwoProfiniteDiagram).π.naturality
      (homOfLE (Nat.le_add_right n 1)).op).symm
    rw [hmap] at hnat
    exact hnat

/-- **The universal property of the actual pro-2 inverse limit**, as Mathlib's
`IsLimit` for the explicit limit cone; it does not use transition surjectivity
or Krull continuity. -/
noncomputable def tatePowerTwoProfiniteLimit_isLimit :
    Limits.IsLimit (ProfiniteGrp.limitCone tatePowerTwoProfiniteDiagram) :=
  ProfiniteGrp.limitConeIsLimit tatePowerTwoProfiniteDiagram

/-- The inverse-system diagram has an actual general limit. -/
theorem tatePowerTwoProfiniteDiagram_hasLimit :
    Limits.HasLimit tatePowerTwoProfiniteDiagram :=
  inferInstance

/-- The lift of an arbitrary cone through the actual limit. -/
noncomputable def tatePowerTwoProfiniteLimitLift
    (c : Limits.Cone tatePowerTwoProfiniteDiagram) :
    c.pt ⟶ tatePowerTwoProfiniteLimit :=
  (ProfiniteGrp.limitConeIsLimit tatePowerTwoProfiniteDiagram).lift c

/-- The lift factors through the actual projections. -/
theorem tatePowerTwoProfiniteLimitLift_fac
    (c : Limits.Cone tatePowerTwoProfiniteDiagram) (n : ℕ) :
    tatePowerTwoProfiniteLimitLift c ≫ tatePowerTwoProfiniteLimitProjection n =
      c.π.app ⟨n⟩ :=
  (ProfiniteGrp.limitConeIsLimit tatePowerTwoProfiniteDiagram).fac c ⟨n⟩

/-- The lift is unique among morphisms with the same projections. -/
theorem tatePowerTwoProfiniteLimitLift_uniq
    (c : Limits.Cone tatePowerTwoProfiniteDiagram)
    (m : c.pt ⟶ tatePowerTwoProfiniteLimit)
    (hm : ∀ n : ℕ, m ≫ tatePowerTwoProfiniteLimitProjection n = c.π.app ⟨n⟩) :
    m = tatePowerTwoProfiniteLimitLift c :=
  (ProfiniteGrp.limitConeIsLimit tatePowerTwoProfiniteDiagram).uniq c m
    (fun j => hm j.unop)

/-! ## Frozen cards -/

/-- **Card 2 (transition surjectivity).**  Every level transition is
surjective.  This is NOT needed for the existence or universal property of the
inverse limit constructed above; it is needed for the later quotient property
`T_2/l^n T_2 = E[2^n]`. -/
def tatePowerTwoTransitionSurjectiveCard : Prop :=
  ∀ n : ℕ, Function.Surjective (tatePowerTwoTransition n)

/-- **Card 3 (Krull continuity).**  A Galois group with the Krull topology
acting continuously on a finite torsion level, with the discrete topology on
the finite level.  This is NOT needed for the abstract inverse limit
constructed above; it is needed for the Galois action on the torsion levels. -/
structure tatePowerTwoGaloisContinuityCard where
  galoisGroup : Type
  [topologicalSpaceGroup : TopologicalSpace galoisGroup]
  [group : Group galoisGroup]
  [compactSpaceGroup : CompactSpace galoisGroup]
  [t2SpaceGroup : T2Space galoisGroup]
  [totallyDisconnectedSpaceGroup : TotallyDisconnectedSpace galoisGroup]
  [topologicalSpaceTarget : TopologicalSpace (tatePowerTwoLevel 3)]
  [discreteTopologyTarget : DiscreteTopology (tatePowerTwoLevel 3)]
  action : galoisGroup → tatePowerTwoLevel 3 → tatePowerTwoLevel 3
  continuous_action : Continuous (Function.uncurry action)

/-- **Odd-`l` torsion criterion (frozen card).**  For an odd prime `l`, all
`l^n`-torsion levels are finite and carry the level transitions of
multiplication by `l`, with the point formula on underlying points. -/
def oddTorsionFinitenessCard (l : ℕ) : Prop :=
  Nat.Prime l ∧ l ≠ 2 ∧
    (∀ n, Finite (LeanFormal.IUT.ABCBridge.Galois.torsionSubgroup
      (curveY2EqX3SubX⁄tateGeometricBase) (l ^ n))) ∧
    (∀ n, ∃ T : LeanFormal.IUT.ABCBridge.Galois.torsionSubgroup
          (curveY2EqX3SubX⁄tateGeometricBase) (l ^ (n + 1)) →+
        LeanFormal.IUT.ABCBridge.Galois.torsionSubgroup
          (curveY2EqX3SubX⁄tateGeometricBase) (l ^ n),
      ∀ P, (T P).1 = (l : ℕ) • P.1)

end Example36
end LeanFormal.IUT.IUTII.Frobenioid
