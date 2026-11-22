/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal IUT/ABC contributors
-/
import LeanFormal.IUT.IUTII.Frobenioid.Example36EllipticCurveSourcePiCard
import LeanFormal.IUT.IUTII.Frobenioid.Example36TorsionAllLevels
import LeanFormal.IUT.IUTII.Frobenioid.Example36OddDivisionPolynomialBounds
import LeanFormal.IUT.Foundations.Geometry.EllipticTorsion

set_option linter.unusedSectionVars false

/-!
# Maximal actual profinite Tate-module data from concrete torsion levels

Task task-62 of the Group-1 continuation.  This module scouts the actualness of
the tree's elliptic LTorsion / galoisLTorsionMatrixRepresentation API,
constructs the largest actual profinite Tate-module data available from the
concrete torsion levels, and freezes the exact missing pro-l inverse-limit data
as a card.

## Scout: what the tree actually has

* PuncturedEllipticCurve.LTorsion X l (Foundations/Geometry/EllipticTorsion.lean)
  is an ACTUAL construction, not an interface field: it is
  AddSubgroup.torsionBy X.AlgebraicClosurePoint l.value, an actual additive
  subgroup of the actual projective points over Mathlib's algebraic closure, and
  it carries a constructed Module (ZMod l.value) instance.  Its elements are
  proved below to be exactly the points killed by l.
* The Galois action is actual: galoisActionOnPoint, galoisActionOnLTorsion,
  the ZMod l-linear equivalence, its monoid-hom form
  galoisActionOnLTorsionLinearEquivHom and the general-linear representation
  galoisActionOnLTorsionGeneralLinearRepresentation are all constructed from
  the actual action on closure-valued points, with no basis hypothesis.
* galoisLTorsionMatrixRepresentation l X basis is an ACTUAL construction but it
  is CONDITIONAL on a supplied rank-two basis
  (Fin 2 -> ZMod l.value) ~= X.LTorsion l; its continuity and its kernel field
  are proved.  Existence of the basis, the exact cardinality #E[l] = l^2 and
  finiteness of E[l] are NOT in the tree (the Audit card
  ellipticLTorsionRankTwoBasis is pending, and Mathlib 4.32.2 has no finiteness
  theorem for elliptic torsion over an algebraic closure).  Hence the profinite
  group structure on E[l] and the matrix representation for l >= 5 cannot be
  instantiated unconditionally; this file builds the actual linear data without
  a basis and freezes the missing rank-two/finiteness datum.

## What is constructed here

1. The concrete punctured curve y^2 = x^3 - x over Q with the origin puncture
   (tatePuncturedCurve), its actual l-torsion tateLevelLTorsion l = E[l] over
   the algebraic closure, the torsion membership criterion, and the actual
   Galois linear, general-linear and basis-conditional matrix representations
   tateLevelLGaloisLinearRepresentation, tateLevelLGaloisGeneralLinearRepresentation
   and tateLevelLGaloisMatrixRepresentation, with the continuity of the matrix
   representation.
2. The already available finite levels E[2] and E[4] are reused (not
   redefined), and the genuine level-transition map [2] : E[4] -> E[2] is
   lifted to the finite discrete profinite groups:
   tateLevelFourToTwoProfinite.
3. The pro-2 inverse limit lim_n E[2^(n+1)] of the actual finite 2-power levels
   is constructed in Example36TorsionAllLevels (N^op diagram with the actual
   transitions [2], Mathlib general small-diagram limit in ProfiniteGrp) and is
   bound here as an actual inhabitant of the corrected card
   ProLTateModuleProjSystemData at l = 2
   (tateTwoProLTateModuleProjSystemData, giving
   ProLTateModuleProjSystemDataRealized 2).  For a general prime l >= 5 the
   pro-l inverse limit / projective system remains the frozen card
   ProLTateModuleProjSystemData (levels, transition maps, limit projections,
   compatibility, universal property, and a binding of level n to the actual
   l^(n+1)-torsion subgroup), since the tree has no E[l^n] levels for n >= 2 and
   no finiteness of E[l].  The full product prod_l T_l(E) is the existing frozen
   source card SourceFullTateModuleData of
   Example36EllipticCurveSourcePiCard.lean; the combined card is
   ProLTateModuleAndFullProductCard.  No general pro-l limit and no product
   group is constructed, and no identification of a Tate module with the
   geometric fundamental group of the once-punctured curve is made.

## Boundary (honest)

The general pro-l Tate module T_l(E) = lim_n E[l^n] is NOT constructed for
l >= 5: the tree has only the single finite level E[l] and no E[l^n] levels for
n >= 2, no finiteness of E[l], no general transition maps E[l^{n+1}] -> E[l^n],
no general limit and no quotient compatibility T_l(E)/l^n T_l(E) = E[l^n].  The
pro-2 inverse limit lim_n E[2^(n+1)] IS constructed for the concrete curve
(Example36TorsionAllLevels) and bound as ProLTateModuleProjSystemData at l = 2;
the level-0 trivia conflict is resolved by indexing levels as E[l^(n+1)]
(level 0 = E[l], not E[1] = 0).  No continuity of a Galois action on a limit is
proved.  The full arithmetic Tate module
prod_l T_l(E) over all primes is likewise not constructed (its card is the
existing SourceFullTateModuleData).  No fake inverse limit is introduced: the
card is data with no inhabitant, and nothing in the tree consumes it.  The
Tate module is abelian and is not the source's nonabelian geometric fundamental
group of the once-punctured curve (the source group is frozen in
SourceCurvePiData / SourceCurvePiCard in Example36EllipticCurveSourcePiCard.lean);
no identification between them is made.  The rank-two basis and the exact
cardinality l^2 for l >= 5 are not proved.  No theta-pilot, q-pilot or further
source identification is claimed.
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36
namespace TateModuleProfinite

open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open CategoryTheory WeierstrassCurve

local instance instDecidableEqTateGeometricBaseTateModule :
    DecidableEq tateGeometricBase :=
  Classical.decEq tateGeometricBase

/-! ## 1. The actual l-torsion of the concrete curve and its Galois action -/

/-- The concrete punctured elliptic curve y^2 = x^3 - x over Q, with the origin
(point at infinity) as puncture. -/
noncomputable def tatePuncturedCurve : PuncturedEllipticCurve ℚ where
  curve := curveY2EqX3SubX
  isElliptic := curveY2EqX3SubX_isElliptic
  puncture := ⟨WeierstrassCurve.Projective.nonsingularLift_zero⟩

/-- The underlying Weierstrass curve of the concrete punctured curve. -/
@[simp]
theorem tatePuncturedCurve_curve :
    tatePuncturedCurve.curve = curveY2EqX3SubX :=
  rfl

/-- The actual l-torsion E[l] of the concrete curve over the algebraic closure,
as the torsion-by-l subgroup of the actual closure-valued points. -/
noncomputable abbrev tateLevelLTorsion (l : PrimeGeFive) :
    AddSubgroup tatePuncturedCurve.AlgebraicClosurePoint :=
  tatePuncturedCurve.LTorsion l

/-- Membership criterion: a closure-valued point lies in E[l] exactly when it
is killed by l. -/
theorem tateLevelLTorsion_mem_iff (l : PrimeGeFive)
    (P : tatePuncturedCurve.AlgebraicClosurePoint) :
    P ∈ tateLevelLTorsion l ↔ l.value • P = 0 :=
  Iff.rfl

/-- Every element of the actual l-torsion is killed by l. -/
theorem tateLevelLTorsion_nsmul (l : PrimeGeFive) (x : tateLevelLTorsion l) :
    l.value • x = 0 :=
  AddSubgroup.torsionBy.nsmul x

/-- The actual l-torsion carries the constructed ZMod l-module structure. -/
@[reducible] noncomputable def tateLevelLTorsionModule (l : PrimeGeFive) :
    Module (ZMod l.value) (tateLevelLTorsion l) :=
  inferInstance

/-- The actual Galois linear action on E[l]: the absolute Galois group of Q acts
by ZMod l-linear automorphisms of the actual torsion module, with no basis
hypothesis. -/
noncomputable def tateLevelLGaloisLinearRepresentation (l : PrimeGeFive) :=
  tatePuncturedCurve.galoisActionOnLTorsionLinearEquivHom l

/-- The actual general-linear representation on E[l], with no basis
hypothesis. -/
noncomputable def tateLevelLGaloisGeneralLinearRepresentation (l : PrimeGeFive) :=
  tatePuncturedCurve.galoisActionOnLTorsionGeneralLinearRepresentation l

/-- The matrix representation, conditional on a rank-two basis.  This is the
actual construction galoisLTorsionMatrixRepresentation specialized to the
concrete curve; the basis is the missing datum of the cards below. -/
noncomputable def tateLevelLGaloisMatrixRepresentation (l : PrimeGeFive)
    (basis : (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value] tateLevelLTorsion l) :=
  tatePuncturedCurve.galoisLTorsionMatrixRepresentation l basis

/-- The kernel of the conditional matrix representation is Krull-open. -/
theorem tateLevelLGaloisMatrixRepresentation_ker_isOpen (l : PrimeGeFive)
    (basis : (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value] tateLevelLTorsion l) :
    IsOpen
      (SetLike.coe (tateLevelLGaloisMatrixRepresentation l basis).ker :
        Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :=
  tatePuncturedCurve.galoisLTorsionMatrixRepresentation_ker_isOpen l basis

/-- The conditional matrix representation is continuous for the Krull
topology. -/
theorem tateLevelLGaloisMatrixRepresentation_continuous (l : PrimeGeFive)
    (basis : (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value] tateLevelLTorsion l) :
    Continuous (tateLevelLGaloisMatrixRepresentation l basis) :=
  tatePuncturedCurve.galoisLTorsionMatrixRepresentation_continuous l basis

/-- **Frozen card: a rank-two basis of E[l].**  Existence of the linear
equivalence (Fin 2 -> ZMod l.value) ~= E[l] is not proved in the tree; the
Audit card ellipticLTorsionRankTwoBasis is pending.  This proposition is a
card, not a theorem, and it is not consumed. -/
def TateLevelLRankTwoBasisCard (l : PrimeGeFive) : Prop :=
  Nonempty ((Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value] tateLevelLTorsion l)

/-- **Frozen card: finiteness of E[l].**  Finiteness (and hence the discrete
profinite group structure on E[l]) is not available for l >= 5 in the tree;
this is a card, not a theorem, and it is not consumed. -/
def TateLevelLFiniteCard (l : PrimeGeFive) : Prop :=
  Finite (tateLevelLTorsion l)

/-! ## 2. The finite levels E[2], E[4] and the genuine transition [2] -/

/-- The monoid-hom form of the genuine level-transition map [2] : E[4] -> E[2],
on the multiplicative encodings used for the finite discrete profinite
groups. -/
noncomputable def tateLevelFourToTwoMonoidHom :
    Multiplicative tateLevelFourTorsion →* Multiplicative tateLevelTwoTorsion where
  toFun x := Multiplicative.ofAdd (multiplicationByTwoFourToTwo (Multiplicative.toAdd x))
  map_one' := by
    apply Multiplicative.ext
    simp
  map_mul' := by
    intro x y
    apply Multiplicative.ext
    change multiplicationByTwoFourToTwo (Multiplicative.toAdd (x * y)) =
      multiplicationByTwoFourToTwo (Multiplicative.toAdd x) +
        multiplicationByTwoFourToTwo (Multiplicative.toAdd y)
    rw [toAdd_mul, map_add]

/-- The level-transition map [2] : E[4] -> E[2] on the finite discrete
profinite groups constructed from the actual finite torsion levels. -/
noncomputable def tateLevelFourToTwoProfinite :
    tateLevelFourProfiniteGroup ⟶ tateLevelTwoProfiniteGroup :=
  ProfiniteGrp.ofFiniteGrpHom (FiniteGrp.ofHom tateLevelFourToTwoMonoidHom)

/-- The underlying function of the profinite transition map is multiplication
by two on the actual 4-torsion. -/
theorem tateLevelFourToTwoProfinite_apply
    (x : (tateLevelFourProfiniteGroup : Type)) :
    (tateLevelFourToTwoProfinite x : (tateLevelTwoProfiniteGroup : Type)) =
      Multiplicative.ofAdd (multiplicationByTwoFourToTwo (Multiplicative.toAdd x)) :=
  rfl

/-- The transition [2] is a map of actual finite groups: the finite level E[4]
is available and its finite discrete profinite structure is the one reused
above.  Its kernel is identified with E[2] by the existing
multiplicationByTwoKerEquiv; this module does not reprove that equivalence. -/
theorem tateLevelFourToTwoProfinite_underlying_additiveHoms
    (x : Multiplicative tateLevelFourTorsion) :
    Multiplicative.toAdd (tateLevelFourToTwoMonoidHom x) =
      multiplicationByTwoFourToTwo (Multiplicative.toAdd x) :=
  rfl

/-! ## 3. The frozen pro-l inverse limit and full product cards -/

/-- **Frozen card: the pro-l Tate module as the inverse limit of the finite
levels.**  The levels are indexed as E[l^(n+1)] (n : Nat), so level 0 is E[l]
and the trivial level E[1] = 0 is omitted; this fixes the former level-0
conflict.  The structure records a projective system of finite discrete
profinite groups together with a binding of level n to the actual
l^(n+1)-torsion subgroup of the concrete curve, the transition maps, the limit
object, compatible projections, and the universal property of the limit.  This
is DATA: for a general l >= 5 no inhabitant is constructed and no theorem
consumes it.  The case l = 2 is inhabited actually by
tateTwoProLTateModuleProjSystemData below. -/
structure ProLTateModuleProjSystemData (l : ℕ) (hl : Nat.Prime l) where
  /-- The finite levels E[l^(n+1)], n : Nat (so level 0 is E[l], not E[1]). -/
  level : ℕ → ProfiniteGrp
  /-- The actual-torsion binding: level n is the l^(n+1)-torsion subgroup of
  the concrete curve, as a multiplicative group. -/
  level_torsion : ∀ n : ℕ,
    Nonempty ((level n : Type) ≃* Multiplicative
      (LeanFormal.IUT.ABCBridge.Galois.torsionSubgroup
        (curveY2EqX3SubX⁄tateGeometricBase) (l ^ (n + 1))))
  /-- The transition maps E[l^(n+1)] -> E[l^n], intended to be multiplication
  by l. -/
  transition : ∀ n : ℕ, level (n + 1) ⟶ level n
  /-- The pro-l Tate module T_l(E). -/
  tateModule : ProfiniteGrp
  /-- The projections from the limit to the finite levels. -/
  projection : ∀ n : ℕ, tateModule ⟶ level n
  /-- The projections are compatible with the transition maps. -/
  projection_compat : ∀ n : ℕ, projection (n + 1) ≫ transition n = projection n
  /-- The universal property of the inverse limit: every compatible cone
  factors uniquely through the Tate module. -/
  limit_unique : ∀ (S : ProfiniteGrp) (q : ∀ n : ℕ, S ⟶ level n),
    (∀ n : ℕ, q (n + 1) ≫ transition n = q n) →
      ∃ u : S ⟶ tateModule,
        (∀ n : ℕ, u ≫ projection n = q n) ∧
          (∀ v : S ⟶ tateModule, (∀ n : ℕ, v ≫ projection n = q n) → v = u)

/-- The pro-l inverse-limit data is realized.  For l = 2 this is PROVED, by
tateTwoProLTateModuleProjSystemData (built from the actual pro-2 limit of
Example36TorsionAllLevels); for l >= 5 it remains a frozen source obligation
and has no consumer in the tree. -/
def ProLTateModuleProjSystemDataRealized (l : ℕ) (hl : Nat.Prime l) : Prop :=
  Nonempty (ProLTateModuleProjSystemData l hl)

/-- **The actual pro-2 Tate system.**  The corrected card
`ProLTateModuleProjSystemData` at `l = 2`, inhabited by the actual finite
levels `E[2^(n+1)]`, the actual transitions `[2]` and the actual general limit
`tatePowerTwoProfiniteLimit` constructed in `Example36TorsionAllLevels`.  This
realizes `ProLTateModuleProjSystemDataRealized 2` unconditionally. -/
noncomputable def tateTwoProLTateModuleProjSystemData :
    ProLTateModuleProjSystemData 2 (by norm_num) where
  level n := tatePowerTwoProfiniteTateLevel n
  level_torsion n := ⟨MulEquiv.refl _⟩
  transition n := tatePowerTwoProfiniteTransition n
  tateModule := tatePowerTwoProfiniteLimit
  projection n := tatePowerTwoProfiniteLimitProjection n
  projection_compat n := tatePowerTwoProfiniteLimitProjection_compatible n
  limit_unique S q hq := by
    let cone : Limits.Cone tatePowerTwoProfiniteDiagram :=
      { pt := S
        π := NatTrans.ofOpSequence (F := (Functor.const ℕᵒᵖ).obj S)
          (G := tatePowerTwoProfiniteDiagram) q (by
            intro n
            rw [show tatePowerTwoProfiniteDiagram.map (homOfLE (Nat.le_add_right n 1)).op =
                tatePowerTwoProfiniteTransition n from by
              exact (Functor.ofOpSequence_map_homOfLE_succ tatePowerTwoProfiniteTransition n)]
            change (𝟙 S) ≫ q n = q (n + 1) ≫ tatePowerTwoProfiniteTransition n
            rw [Category.id_comp]
            exact (hq n).symm) }
    refine ⟨(ProfiniteGrp.limitConeIsLimit tatePowerTwoProfiniteDiagram).lift cone, ?_, ?_⟩
    · intro n
      exact (ProfiniteGrp.limitConeIsLimit tatePowerTwoProfiniteDiagram).fac cone ⟨n⟩
    · intro v hv
      exact (ProfiniteGrp.limitConeIsLimit tatePowerTwoProfiniteDiagram).uniq cone v
        (fun j => hv j.unop)

/-- The pro-2 inverse-limit data is realized (actual, unconditional). -/
theorem proLTateModuleProjSystemDataRealized_two :
    ProLTateModuleProjSystemDataRealized 2 (by norm_num) :=
  ⟨tateTwoProLTateModuleProjSystemData⟩

/-- The full product prod_l T_l(E) over all primes is the existing frozen source
card SourceFullTateModuleData of the concrete once-punctured curve, reused here
(not redefined and not constructed). -/
def FullProductTateModuleCard : Prop :=
  SourceFullTateModuleDataRealized sourceOncePuncturedEllipticCurve

/-- **The combined frozen card**: for a prime l, the pro-l inverse-limit data
and the full product prod_l T_l(E).  This is a card, not a theorem; it has no
inhabitant and no consumer. -/
def ProLTateModuleAndFullProductCard (l : ℕ) (hl : Nat.Prime l) : Prop :=
  ProLTateModuleProjSystemDataRealized l hl ∧ FullProductTateModuleCard

/-! ## 4. The maximal actual profinite data for l >= 5 -/

/-- **The maximal actual data at l >= 5.**  Unconditionally, the actual
ZMod l-module E[l] and its actual Galois linear and general-linear
representations are available; the matrix representation is available exactly
when a rank-two basis is supplied.  This theorem is a bundling of the real
constructions above, not a claim of finiteness or of a basis. -/
theorem tateLevelL_maximalActualData (l : PrimeGeFive) :
    Nonempty (Module (ZMod l.value) (tateLevelLTorsion l)) ∧
      Nonempty (Gal(AlgebraicClosure ℚ/ℚ) →*
        (tateLevelLTorsion l ≃ₗ[ZMod l.value] tateLevelLTorsion l)) ∧
      (∀ _ : (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value] tateLevelLTorsion l,
        Nonempty (Gal(AlgebraicClosure ℚ/ℚ) →* GL (Fin 2) (ZMod l.value))) :=
  ⟨⟨tateLevelLTorsionModule l⟩,
    ⟨tateLevelLGaloisLinearRepresentation l⟩,
    fun basis => ⟨tateLevelLGaloisMatrixRepresentation l basis⟩⟩

/-- The rank-two basis card is not proved: this is the exact missing
datum behind the conditional matrix representation. -/
def tateLevelL_rankTwoBasisIsMissing (l : PrimeGeFive) : Prop :=
  TateLevelLRankTwoBasisCard l

/-! ## 5. Rank two from the cardinality `l ^ 2`: the linear-algebra engine

The rank-two basis card `TateLevelLRankTwoBasisCard` is *not* an independent
input: for a finite `ZMod l`-module of cardinality `l ^ 2` the `ZMod l`-dimension
is forced to be two and a basis exists.  The two lemmas below are that engine,
unconditional and reusable.  They reduce the whole rank-two/basis problem for a
level `l` to the single numerical input `Nat.card E[l] = l ^ 2` (plus finiteness,
which is *not* implied by `Nat.card`, since `Nat.card` of an infinite type is the
junk value `0`). -/

/-- A finite `ZMod l`-module of cardinality `l ^ 2` has `ZMod l`-dimension two. -/
theorem zmod_finrank_eq_two_of_natCard_eq_sq {l : ℕ} [Fact (Nat.Prime l)]
    (V : Type*) [AddCommGroup V] [Module (ZMod l) V] [Finite V]
    (hcard : Nat.card V = l ^ 2) :
    Module.finrank (ZMod l) V = 2 := by
  haveI : Module.Finite (ZMod l) V := Module.Finite.of_finite (R := ZMod l) (M := V)
  have hmain : l ^ 2 = l ^ Module.finrank (ZMod l) V := by
    rw [← hcard, Module.natCard_eq_pow_finrank (K := ZMod l) (V := V), Nat.card_zmod]
  have hl : 1 < l := (Fact.out : Nat.Prime l).one_lt
  rcases lt_trichotomy (Module.finrank (ZMod l) V) 2 with hlt | heq | hgt
  · have hlt' : l ^ Module.finrank (ZMod l) V < l ^ 2 :=
      Nat.pow_lt_pow_right hl hlt
    omega
  · exact heq
  · have hgt' : l ^ 2 < l ^ Module.finrank (ZMod l) V :=
      Nat.pow_lt_pow_right hl hgt
    omega

/-- A finite `ZMod l`-module of cardinality `l ^ 2` has a `Fin 2`-indexed basis. -/
theorem nonempty_basis_fin_two_of_natCard_eq_sq {l : ℕ} [Fact (Nat.Prime l)]
    (V : Type*) [AddCommGroup V] [Module (ZMod l) V] [Finite V]
    (hcard : Nat.card V = l ^ 2) :
    Nonempty (Module.Basis (Fin 2) (ZMod l) V) := by
  haveI : Module.Finite (ZMod l) V := Module.Finite.of_finite (R := ZMod l) (M := V)
  exact ⟨Module.finBasisOfFinrankEq (ZMod l) V
    (zmod_finrank_eq_two_of_natCard_eq_sq V hcard)⟩

/-! ## 6. The reduction of the l >= 5 cards to the numerical input `Nat.card = l ^ 2`

`TateLevelLCardinalityCard` names the exact numerical datum.  It implies the
older `TateLevelLFiniteCard` card and the *basis form* of the rank-two datum;
hence the rank-two basis is not an independent obligation, only the cardinality
`l ^ 2` is.  The cardinality itself is not proved here for `l >= 5`; it is the
precise remaining gap (see section 7 for the unconditional `l = 3` case).

The older `TateLevelLRankTwoBasisCard` is the `LinearEquiv`-shaped form of the
same datum.  A basis yields such an equivalence through `Module.Basis.equivFun`
(`TateLevelLRankTwoLinearEquivOfBasis`); we do not transport the cardinality
result across the two presentations here, because the two statements were
elaborated with syntactically different (though mathematically identical)
`Semiring (ZMod l.value)` instance paths. -/

/-- **Frozen card: the exact cardinality of the concrete `l`-torsion.**  Both
finiteness and `Nat.card E[l] = l ^ 2` are required, because `Nat.card` of an
infinite type is `0`.  Not proved for `l >= 5` in the tree; proved
unconditionally for `l = 3` in section 7. -/
def TateLevelLCardinalityCard (l : PrimeGeFive) : Prop :=
  Finite (tateLevelLTorsion l) ∧ Nat.card (tateLevelLTorsion l) = l.value ^ 2

/-- The cardinality card implies the old finiteness card. -/
theorem tateLevelLFiniteCard_of_cardinalityCard (l : PrimeGeFive)
    (h : TateLevelLCardinalityCard l) : TateLevelLFiniteCard l :=
  h.1

/-- **The rank-two basis exists as soon as the cardinality is `l ^ 2`.**  This
is the actual `Module.Basis` form of the rank-two datum; it shows that the
basis is not an independent obligation but a consequence of the numerical
input `TateLevelLCardinalityCard`. -/
theorem nonempty_basis_of_cardinalityCard (l : PrimeGeFive)
    (h : TateLevelLCardinalityCard l) :
    Nonempty (Module.Basis (Fin 2) (ZMod l.value) (tateLevelLTorsion l)) := by
  haveI : Finite (tateLevelLTorsion l) := h.1
  haveI : Fact (Nat.Prime l.value) := l.factPrime
  exact nonempty_basis_fin_two_of_natCard_eq_sq (tateLevelLTorsion l) h.2

/-- A basis of the concrete `l`-torsion, in the `LinearEquiv` presentation used
by `galoisLTorsionMatrixRepresentation`. -/
theorem TateLevelLRankTwoLinearEquivOfBasis (l : PrimeGeFive)
    (b : Module.Basis (Fin 2) (ZMod l.value) (tateLevelLTorsion l)) :
    Nonempty ((Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value] tateLevelLTorsion l) :=
  ⟨b.equivFun.symm⟩

/-- The `ZMod l`-dimension of the concrete `l`-torsion is two as soon as the
cardinality is `l ^ 2`. -/
theorem tateLevelLFinrank_eq_two_of_cardinalityCard (l : PrimeGeFive)
    (h : TateLevelLCardinalityCard l) :
    Module.finrank (ZMod l.value) (tateLevelLTorsion l) = 2 := by
  haveI : Finite (tateLevelLTorsion l) := h.1
  haveI : Fact (Nat.Prime l.value) := l.factPrime
  exact zmod_finrank_eq_two_of_natCard_eq_sq (tateLevelLTorsion l) h.2

/-! ## 7. The unconditional concrete level `l = 3`

The group-law criterion `l • P = 0 <-> psi_l(P) = 0` is proved in the tree only
for `l = 3` (`three_nsmul_eq_zero_iff`), so `l = 3` is the one odd prime for
which the cardinality `l ^ 2` can currently be proved unconditionally.  This
section does exactly that: `Nat.card E[3] = 9`, `finrank (ZMod 3) E[3] = 2`, and
an actual `Fin 2`-indexed basis.  The proof is the general division-polynomial
argument (candidates: the origin together with a root `x` of the quartic psi_3
and a square root `y` of `x ^ 3 - x`) carried out with explicit roots: the
square roots of `1 + (2/3) sqrt 3` and `1 - (2/3) sqrt 3` give four distinct
roots of psi_3 = 3 X^4 - 6 X^2 - 1, each with two distinct y-values. -/

/-- The base field of the concrete level-three computation: the algebraic
closure of `Q`. -/
abbrev tateClosureField : Type := AlgebraicClosure ℚ

open LeanFormal.IUT.IUTII.Frobenioid.Example36.DivisionTorsionThree
open Polynomial

local instance tateClosureFieldDecidableEq : DecidableEq tateClosureField :=
  Classical.decEq _

local instance tateLevelThreePointDecidableEq :
    DecidableEq ((y2x3xCurve (K := tateClosureField)).toAffine.Point) :=
  Classical.decEq _

/-- The concrete level-three torsion subgroup over the algebraic closure. -/
abbrev tateLevelThreeTorsion :
    AddSubgroup ((y2x3xCurve (K := tateClosureField)).toAffine.Point) :=
  AddSubgroup.torsionBy _ 3

/-- The level-three torsion is the tree's `threeTorsionSubgroup` at the
algebraic closure. -/
theorem tateLevelThreeTorsion_eq_threeTorsionSubgroup :
    tateLevelThreeTorsion = DivisionTorsionThree.threeTorsionSubgroup tateClosureField :=
  rfl

/-- psi_3 is nonzero over the algebraic closure of `Q`. -/
theorem tateLevelThree_Ψ₃_ne_zero :
    (y2x3xCurve (K := tateClosureField)).Ψ₃ ≠ 0 :=
  OddTorsionFiniteness.y2x3xCurve_Ψ₃_ne_zero (K := tateClosureField)

/-- If `x ^ 2 = u` and `3 u ^ 2 - 6 u - 1 = 0`, then `psi_3` vanishes at `x`. -/
theorem tateLevelThree_Ψ₃_eval_eq_zero_of_sq {x u : tateClosureField}
    (hx : x ^ 2 = u) (hu : 3 * u ^ 2 - 6 * u - 1 = 0) :
    (y2x3xCurve (K := tateClosureField)).Ψ₃.eval x = 0 := by
  rw [DivisionTorsionThree.y2x3xCurve_eval_Ψ₃]
  rw [show x ^ 4 = (x ^ 2) ^ 2 by ring, hx]
  exact hu

/-- **Four distinct roots of psi_3 over the algebraic closure.**  The roots are
the square roots of `1 + (2/3) s` and `1 - (2/3) s`, where `s ^ 2 = 3`. -/
theorem tateLevelThree_exists_four_roots :
    ∃ x₁ x₂ x₃ x₄ : tateClosureField,
      x₁ ≠ x₂ ∧ x₁ ≠ x₃ ∧ x₁ ≠ x₄ ∧ x₂ ≠ x₃ ∧ x₂ ≠ x₄ ∧ x₃ ≠ x₄ ∧
        (∀ x ∈ ({x₁, x₂, x₃, x₄} : Finset tateClosureField),
          (y2x3xCurve (K := tateClosureField)).Ψ₃.eval x = 0) := by
  classical
  obtain ⟨s, hs⟩ :=
    IsAlgClosed.exists_pow_nat_eq (3 : tateClosureField) (by norm_num : 0 < 2)
  obtain ⟨t₁, ht₁⟩ :=
    IsAlgClosed.exists_pow_nat_eq (1 + (2 / 3) * s) (by norm_num : 0 < 2)
  obtain ⟨t₂, ht₂⟩ :=
    IsAlgClosed.exists_pow_nat_eq (1 - (2 / 3) * s) (by norm_num : 0 < 2)
  have hq₁ : 3 * (1 + (2 / 3) * s) ^ 2 - 6 * (1 + (2 / 3) * s) - 1 = 0 := by
    linear_combination (4 / 3) * hs
  have hq₂ : 3 * (1 - (2 / 3) * s) ^ 2 - 6 * (1 - (2 / 3) * s) - 1 = 0 := by
    linear_combination (4 / 3) * hs
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hs43 : ((4 : tateClosureField) / 3) ≠ 0 := by norm_num
  have hu_ne : (1 + (2 / 3) * s) ≠ (1 - (2 / 3) * s) := by
    intro h
    have hzero : (4 / 3) * s = 0 := by linear_combination h
    exact hs0 ((mul_eq_zero.mp hzero).resolve_left hs43)
  have hu₁0 : (1 + (2 / 3) * s) ≠ 0 := by
    intro h
    have hs' : s = -(3 / 2) := by linear_combination (3 / 2) * h
    rw [hs'] at hs
    norm_num at hs
  have hu₂0 : (1 - (2 / 3) * s) ≠ 0 := by
    intro h
    have hs' : s = 3 / 2 := by linear_combination (-(3 / 2)) * h
    rw [hs'] at hs
    norm_num at hs
  have ht₁0 : t₁ ≠ 0 := by
    intro h
    exact hu₁0 (by rw [← ht₁, h]; ring)
  have ht₂0 : t₂ ≠ 0 := by
    intro h
    exact hu₂0 (by rw [← ht₂, h]; ring)
  have h₁₂ : t₁ ≠ -t₁ := by
    intro h
    exact ht₁0 (by linear_combination (1 / 2) * h)
  have h₃₄ : t₂ ≠ -t₂ := by
    intro h
    exact ht₂0 (by linear_combination (1 / 2) * h)
  have hsq_ne : t₁ ^ 2 ≠ t₂ ^ 2 := by
    intro h
    rw [ht₁, ht₂] at h
    have hzero : (4 / 3) * s = 0 := by linear_combination h
    exact hs0 ((mul_eq_zero.mp hzero).resolve_left hs43)
  have h₁₃ : t₁ ≠ t₂ := by
    intro h
    exact hsq_ne (by rw [h])
  have h₁₄ : t₁ ≠ -t₂ := by
    intro h
    exact hsq_ne (by rw [h]; ring)
  have h₂₃ : -t₁ ≠ t₂ := by
    intro h
    have h' : t₂ = -t₁ := by linear_combination -h
    exact hsq_ne (by rw [h']; ring)
  have h₂₄ : -t₁ ≠ -t₂ := by
    intro h
    have h' : t₁ = t₂ := by linear_combination -h
    exact hsq_ne (by rw [h'])
  have hroot₁ : (y2x3xCurve (K := tateClosureField)).Ψ₃.eval t₁ = 0 :=
    tateLevelThree_Ψ₃_eval_eq_zero_of_sq ht₁ hq₁
  have hroot₂ : (y2x3xCurve (K := tateClosureField)).Ψ₃.eval (-t₁) = 0 :=
    tateLevelThree_Ψ₃_eval_eq_zero_of_sq
      (by rw [show (-t₁) ^ 2 = t₁ ^ 2 by ring, ht₁]) hq₁
  have hroot₃ : (y2x3xCurve (K := tateClosureField)).Ψ₃.eval t₂ = 0 :=
    tateLevelThree_Ψ₃_eval_eq_zero_of_sq ht₂ hq₂
  have hroot₄ : (y2x3xCurve (K := tateClosureField)).Ψ₃.eval (-t₂) = 0 :=
    tateLevelThree_Ψ₃_eval_eq_zero_of_sq
      (by rw [show (-t₂) ^ 2 = t₂ ^ 2 by ring, ht₂]) hq₂
  exact ⟨t₁, -t₁, t₂, -t₂, h₁₂, h₁₃, h₁₄, h₂₃, h₂₄, h₃₄,
    fun x hx => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      exacts [hroot₁, hroot₂, hroot₃, hroot₄]⟩

/-- psi_3 has at most four roots over the algebraic closure. -/
theorem tateLevelThree_Ψ₃_roots_card_le_four :
    ((y2x3xCurve (K := tateClosureField)).Ψ₃.roots.toFinset).card ≤ 4 :=
  (Multiset.toFinset_card_le _).trans
    ((Polynomial.card_roots' _).trans (WeierstrassCurve.natDegree_Ψ₃_le _))

/-- psi_3 has at least four roots over the algebraic closure. -/
theorem tateLevelThree_Ψ₃_roots_card_ge_four :
    4 ≤ ((y2x3xCurve (K := tateClosureField)).Ψ₃.roots.toFinset).card := by
  obtain ⟨x₁, x₂, x₃, x₄, h₁₂, h₁₃, h₁₄, h₂₃, h₂₄, h₃₄, hroot⟩ :=
    tateLevelThree_exists_four_roots
  have hsub : ({x₁, x₂, x₃, x₄} : Finset tateClosureField) ⊆
      (y2x3xCurve (K := tateClosureField)).Ψ₃.roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset,
      Polynomial.mem_roots tateLevelThree_Ψ₃_ne_zero]
    exact hroot x hx
  have hcard : ({x₁, x₂, x₃, x₄} : Finset tateClosureField).card = 4 := by
    have h1 : x₁ ∉ ({x₂, x₃, x₄} : Finset tateClosureField) := by
      simp [h₁₂, h₁₃, h₁₄]
    have h2 : x₂ ∉ ({x₃, x₄} : Finset tateClosureField) := by
      simp [h₂₃, h₂₄]
    have h3 : x₃ ∉ ({x₄} : Finset tateClosureField) := by
      simp [h₃₄]
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
      Finset.card_insert_of_notMem h3, Finset.card_singleton]
  calc 4 = ({x₁, x₂, x₃, x₄} : Finset tateClosureField).card := hcard.symm
    _ ≤ _ := Finset.card_le_card hsub

/-- psi_3 has exactly four roots over the algebraic closure. -/
theorem tateLevelThree_Ψ₃_roots_card :
    ((y2x3xCurve (K := tateClosureField)).Ψ₃.roots.toFinset).card = 4 :=
  le_antisymm tateLevelThree_Ψ₃_roots_card_le_four tateLevelThree_Ψ₃_roots_card_ge_four

/-- At a root `x` of psi_3 the value `x ^ 3 - x` is nonzero, so the equation
`y ^ 2 = x ^ 3 - x` has exactly two solutions over the algebraic closure. -/
theorem tateLevelThree_fiber_card {x : tateClosureField}
    (hx : x ∈ (y2x3xCurve (K := tateClosureField)).Ψ₃.roots.toFinset) :
    ((Polynomial.X ^ 2 - Polynomial.C (x ^ 3 - x) : tateClosureField[X]).roots.toFinset).card =
      2 := by
  classical
  have hxeval : (y2x3xCurve (K := tateClosureField)).Ψ₃.eval x = 0 :=
    OddTorsionFiniteness.y2x3xCurve_eval_Ψ₃_of_mem_roots hx
  have hc : x ^ 3 - x ≠ 0 := by
    intro h0
    have hfac : x * (x - 1) * (x + 1) = 0 := by
      have h : x * (x - 1) * (x + 1) = x ^ 3 - x := by ring
      rw [h, h0]
    rcases mul_eq_zero.mp hfac with hx1 | hx1
    · rcases mul_eq_zero.mp hx1 with hx2 | hx2
      · have hx0 : x = 0 := by linear_combination hx2
        rw [hx0, DivisionTorsionThree.y2x3xCurve_eval_Ψ₃] at hxeval
        norm_num at hxeval
      · have hx1' : x = 1 := by linear_combination hx2
        rw [hx1', DivisionTorsionThree.y2x3xCurve_eval_Ψ₃] at hxeval
        norm_num at hxeval
    · have hxneg : x = -1 := by linear_combination hx1
      rw [hxneg, DivisionTorsionThree.y2x3xCurve_eval_Ψ₃] at hxeval
      norm_num at hxeval
  have hne : (Polynomial.X ^ 2 - Polynomial.C (x ^ 3 - x) : tateClosureField[X]) ≠ 0 :=
    Polynomial.X_pow_sub_C_ne_zero (by norm_num : 0 < 2) (x ^ 3 - x)
  have hle : ((Polynomial.X ^ 2 - Polynomial.C (x ^ 3 - x) :
      tateClosureField[X]).roots.toFinset).card ≤ 2 :=
    (Multiset.toFinset_card_le _).trans
      ((Polynomial.card_roots' _).trans (by rw [Polynomial.natDegree_X_pow_sub_C]))
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (x ^ 3 - x) (by norm_num : 0 < 2)
  have hy0 : y ≠ 0 := by
    intro h
    exact hc (by rw [← hy, h]; ring)
  have hyn : y ≠ -y := by
    intro h
    exact hy0 (by linear_combination (1 / 2) * h)
  have hmem₁ : y ∈ ((Polynomial.X ^ 2 - Polynomial.C (x ^ 3 - x) :
      tateClosureField[X]).roots.toFinset) := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hne]
    simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C]
    rw [hy]
    ring
  have hmem₂ : -y ∈ ((Polynomial.X ^ 2 - Polynomial.C (x ^ 3 - x) :
      tateClosureField[X]).roots.toFinset) := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hne]
    simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C]
    rw [show (-y) ^ 2 = y ^ 2 by ring, hy]
    ring
  have hge : 2 ≤ ((Polynomial.X ^ 2 - Polynomial.C (x ^ 3 - x) :
      tateClosureField[X]).roots.toFinset).card := by
    have hsub : ({y, -y} : Finset tateClosureField) ⊆
        ((Polynomial.X ^ 2 - Polynomial.C (x ^ 3 - x) : tateClosureField[X]).roots.toFinset) := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      exacts [hmem₁, hmem₂]
    have hcard : ({y, -y} : Finset tateClosureField).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simpa using hyn), Finset.card_singleton]
    calc 2 = ({y, -y} : Finset tateClosureField).card := hcard.symm
      _ ≤ _ := Finset.card_le_card hsub
  omega

/-- The cardinality of the subtype of members of a finset is the cardinality of
the finset. -/
theorem natCard_subtype_mem_finset {α : Type*} (s : Finset α) :
    Nat.card {x : α // x ∈ s} = s.card := by
  have h : Nat.card {x : α // x ∈ s} = (s : Set α).ncard := rfl
  rw [h, Set.ncard_coe_finset]

/-- The level-three candidate index type has eight elements: four roots of
psi_3, each with two y-values. -/
theorem tateLevelThree_candidateIndex_natCard :
    Nat.card (OddTorsionFiniteness.threeTorsionCandidateIndex tateClosureField) = 8 := by
  classical
  rw [Nat.card_sigma]
  have hfiber : ∀ x : {x : tateClosureField //
      x ∈ (y2x3xCurve (K := tateClosureField)).Ψ₃.roots.toFinset},
      Nat.card {y : tateClosureField // y ∈
        (Polynomial.X ^ 2 - Polynomial.C (x.1 ^ 3 - x.1) : tateClosureField[X]).roots.toFinset} =
        2 := by
    intro x
    rw [natCard_subtype_mem_finset, tateLevelThree_fiber_card x.2]
  rw [Finset.sum_congr rfl (fun x _ => hfiber x), Finset.sum_const, Finset.card_univ,
    Fintype.card_eq_nat_card, natCard_subtype_mem_finset, tateLevelThree_Ψ₃_roots_card]
  norm_num

/-- The explicit finite set of level-three candidates, elaborated in this
file's context: the origin together with all points `(x, y)` with `psi_3 x = 0`
and `y ^ 2 = x ^ 3 - x`. -/
noncomputable def tateLevelThreeCandidatePoints :
    Finset ((y2x3xCurve (K := tateClosureField)).toAffine.Point) :=
  insert 0 (Finset.univ.image
    (OddTorsionFiniteness.threeTorsionCandidatePoint (K := tateClosureField)
      (by norm_num : (2 : tateClosureField) ≠ 0)))

/-- The candidate set of the level-three torsion has nine elements. -/
theorem tateLevelThreeCandidatePoints_card : tateLevelThreeCandidatePoints.card = 9 := by
  classical
  have h2ne : (2 : tateClosureField) ≠ 0 := by norm_num
  have hinj : Function.Injective
      (OddTorsionFiniteness.threeTorsionCandidatePoint (K := tateClosureField) h2ne) := by
    rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ ⟨⟨x', hx'⟩, ⟨y', hy'⟩⟩ heq
    simp only [OddTorsionFiniteness.threeTorsionCandidatePoint] at heq
    rw [WeierstrassCurve.Affine.Point.some.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    rfl
  have hnot : (0 : (y2x3xCurve (K := tateClosureField)).toAffine.Point) ∉
      Finset.univ.image
        (OddTorsionFiniteness.threeTorsionCandidatePoint (K := tateClosureField) h2ne) := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    rintro ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, hp⟩
    simp only [OddTorsionFiniteness.threeTorsionCandidatePoint] at hp
    exact (WeierstrassCurve.Affine.Point.some_ne_zero _) hp
  have h1 : (Finset.univ.image
      (OddTorsionFiniteness.threeTorsionCandidatePoint (K := tateClosureField) h2ne)).card =
      8 := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_eq_nat_card,
      tateLevelThree_candidateIndex_natCard]
  rw [tateLevelThreeCandidatePoints, Finset.card_insert_of_notMem hnot, h1]

/-- The candidate set is, as a set, the tree's `threeTorsionCandidates`. -/
theorem tateLevelThreeCandidatePoints_coe :
    (↑(OddTorsionFiniteness.threeTorsionCandidates (K := tateClosureField)
        (by norm_num : (2 : tateClosureField) ≠ 0)) :
        Set ((y2x3xCurve (K := tateClosureField)).toAffine.Point)) =
      ↑tateLevelThreeCandidatePoints := by
  ext P
  simp only [Finset.mem_coe, OddTorsionFiniteness.threeTorsionCandidates,
    tateLevelThreeCandidatePoints, Finset.mem_insert, Finset.mem_singleton,
    Finset.mem_image, Finset.mem_univ, true_and]

/-- **The concrete level-three torsion has cardinality nine.** -/
theorem tateLevelThree_natCard : Nat.card tateLevelThreeTorsion = 9 := by
  classical
  have h2ne : (2 : tateClosureField) ≠ 0 := by norm_num
  have hset : (tateLevelThreeTorsion :
      Set ((y2x3xCurve (K := tateClosureField)).toAffine.Point)) =
      ↑tateLevelThreeCandidatePoints := by
    rw [tateLevelThreeTorsion_eq_threeTorsionSubgroup,
      OddTorsionFiniteness.threeTorsionSubgroup_eq_candidates (K := tateClosureField) h2ne]
    exact tateLevelThreeCandidatePoints_coe
  calc Nat.card tateLevelThreeTorsion
      = (tateLevelThreeTorsion :
          Set ((y2x3xCurve (K := tateClosureField)).toAffine.Point)).ncard :=
        Nat.card_coe_set_eq _
    _ = (↑tateLevelThreeCandidatePoints :
          Set ((y2x3xCurve (K := tateClosureField)).toAffine.Point)).ncard := by rw [hset]
    _ = tateLevelThreeCandidatePoints.card := Set.ncard_coe_finset _
    _ = 9 := tateLevelThreeCandidatePoints_card

local instance tateLevelThreeTorsionModule : Module (ZMod 3) tateLevelThreeTorsion :=
  AddSubgroup.torsionBy.zmodModule

local instance tateLevelThreeTorsionFinite : Finite tateLevelThreeTorsion := by
  rw [tateLevelThreeTorsion_eq_threeTorsionSubgroup]
  infer_instance

/-- **The concrete level-three torsion is a two-dimensional `ZMod 3`-space.** -/
theorem tateLevelThree_finrank : Module.finrank (ZMod 3) tateLevelThreeTorsion = 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hcard : Nat.card tateLevelThreeTorsion = 3 ^ 2 := by
    rw [tateLevelThree_natCard]
    norm_num
  exact zmod_finrank_eq_two_of_natCard_eq_sq tateLevelThreeTorsion hcard

/-- **The concrete level-three torsion has an actual `Fin 2`-indexed basis over
`ZMod 3`.**  This is the first unconditional rank-two Tate-level datum of the
tree (at the only odd prime for which the group-law criterion is proved). -/
theorem tateLevelThree_nonempty_basis :
    Nonempty (Module.Basis (Fin 2) (ZMod 3) tateLevelThreeTorsion) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hcard : Nat.card tateLevelThreeTorsion = 3 ^ 2 := by
    rw [tateLevelThree_natCard]
    norm_num
  exact nonempty_basis_fin_two_of_natCard_eq_sq tateLevelThreeTorsion hcard

end TateModuleProfinite
end Example36
end LeanFormal.IUT.IUTII.Frobenioid

namespace LeanFormal.IUT.Audit

/-- Audit record for task-62. -/
def example36TateModuleProfinite : Obligation :=
  { id := "IUT-II.example36-tate-module-profinite-data"
    source :=
      "IUT II, Sections 3-6 (Tate modules); Tree foundations geometry elliptic torsion"
    status := VerificationStatus.interface
    note :=
      "SCOUT: PuncturedEllipticCurve.LTorsion and galoisLTorsionMatrixRepresentation " ++
        "are actual constructions (torsionBy of actual closure points; actual " ++
        "linear Galois action; matrix form conditional on a supplied rank-two " ++
        "basis).  CONSTRUCTED: the concrete punctured curve y^2 = x^3 - x over Q, " ++
        "its actual E[l]-module and actual Galois linear/general-linear " ++
        "representations for l >= 5, the continuation of the actual finite levels " ++
        "E[2], E[4] and the genuine transition [2] on the finite discrete " ++
        "profinite groups.  CORRECTED/ACTUAL (F-R5): the pro-2 inverse limit " ++
        "lim_n E[2^(n+1)] as an N^op diagram with the actual transitions [2], " ++
        "Mathlib general limit, projections, compatibility and universal " ++
        "property (Example36TorsionAllLevels), and an actual inhabitant " ++
        "ProLTateModuleProjSystemData at l = 2 " ++
        "(tateTwoProLTateModuleProjSystemData, " ++
        "proLTateModuleProjSystemDataRealized_two); the card levels are " ++
        "reindexed E[l^(n+1)] (level 0 = E[l], no E[1] conflict) and bound to " ++
        "the actual l^(n+1)-torsion subgroup by level_torsion.  MISSING " ++
        "(frozen cards, l >= 5): existence of the rank-two basis and " ++
        "finiteness of E[l] (TateLevelLRankTwoBasisCard, " ++
        "TateLevelLFiniteCard), the general pro-l transition system and " ++
        "inverse limit, and the full product prod_l T_l(E) (existing " ++
        "SourceFullTateModuleData card).  For l >= 5 no inverse limit is " ++
        "faked; the l = 2 limit is actual.  No Tate module is identified " ++
        "with the nonabelian geometric fundamental group of the " ++
        "once-punctured curve."
    dependsOn :=
      [ "Foundations.Geometry.elliptic-torsion-galois",
        "IUT-I-II.example36-elliptic-curve-anabelioid",
        "IUT-I-II.example36-elliptic-curve-tate-higher-level",
        "IUT-I-II.example36-source-curve-pi-card" ] }

end LeanFormal.IUT.Audit
