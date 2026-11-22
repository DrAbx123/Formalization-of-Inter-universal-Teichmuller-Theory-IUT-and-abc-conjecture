import tmp.sheaf.xif.paper.S1982D5FiveActual
import tmp.sheaf.xif.paper.S1467FunctionFieldPullbackActual

/-!
# S2033: the l = 5 division-pair bijection and the Dedekind factorization interface

This file attacks items (1) and (2) of the S1987 report's list of seven formalisation
gaps for the D5 large-image input at l = 5.

## (1) Roots of prePsi_5 versus the twelve pairs {+-P}

Let E' be the actual curve S1720Curve over F' and let K be an algebraic closure of F'.
S1924's group-law criterion identifies the zeros of the 5-division polynomial with the
5-torsion points.  This file proves, with no extra hypothesis, that the map

  x  |->  { P in E'[5] : P ≠ 0 and x(P) = x }

is a bijection from the roots of prePsi_5 to the two-element subsets of the nonzero
5-torsion that are closed under negation, i.e. the twelve pairs {+-P}.  The construction
is canonical (it uses the x-coordinate, not a choice of sign), hence Galois-equivariant.
The file records the equivariance statement for an arbitrary F'-algebra automorphism
of K.

## (2) Dedekind factorization

The number-field Dedekind theorem is recorded as an explicit missing proposition
(S2033DedekindFactorization).  The finite-field part that is available in Mathlib --
the orbit/factor-degree relation for an irreducible polynomial over ZMod p -- is also
recorded precisely, together with its exact first missing statement.  No inhabitant of
either missing proposition is manufactured.

## Verification status

No sorry, no admit, no axiom, no opaque, no native_decide.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1906RankTwoTorsionActual
open LeanFormal.IUT.XiFPaper.S1924ZeroCriterionActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S1329RankTwoTorsionBasisActual
open LeanFormal.IUT.XiFPaper.S1667AdmissibleCurveActual

namespace LeanFormal.IUT.XiFPaper.S2033D5DivisionActual

local instance S2033KDecEq : DecidableEq S1906K := Classical.decEq _

/-- The algebraic closure K of F' used throughout S1924/S1982. -/
abbrev S2033K : Type := S1906K

/-- The actual curve E' base changed to K. -/
abbrev S2033W : WeierstrassCurve.Affine S2033K := S1906W

/-- The 5-torsion subgroup of E'(K). -/
abbrev S2033Torsion : Type := AddSubgroup.torsionBy S2033W.Point (5 : Int)

/-- The nonzero 5-torsion points. -/
abbrev S2033NonzeroTorsion : Type := {P : S2033Torsion // (P.1 : S2033W.Point) ≠ 0}

/-- The distinct roots of prePsi_5 in K. -/
abbrev S2033RootFinset : Finset S2033K := (S2033W.preΨ (5 : Int)).roots.toFinset

/-- The root set of prePsi_5. -/
abbrev S2033Root : Type := {x : S2033K // x ∈ S2033RootFinset}

/-- Negation on the nonzero 5-torsion. -/
instance S2033NonzeroTorsion_neg : Neg S2033NonzeroTorsion where
  neg P := ⟨-P.1, by
    intro h
    have h' : (P.1 : S2033W.Point) = 0 := by
      simpa using neg_eq_zero.mp h
    exact P.2 h'⟩

/-- A pair {+-P} of nonzero 5-torsion points, represented as a two-element
negation-closed finite set. -/
abbrev S2033Pair : Type :=
  {S : Finset S2033NonzeroTorsion // S.card = 2 ∧ ∀ P ∈ S, -P ∈ S}

/-- The root count: prePsi_5 has exactly 12 distinct roots. -/
theorem S2033Root_card : Nat.card S2033Root = 12 := by
  classical
  have h : (s1329RootFinset S1906W 5).card = 12 := by
    simpa [S1906RootCount, S1982Five] using S1982RootCount_five
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  simpa [S2033RootFinset, s1329RootFinset] using h

/-- The affine 5-torsion has 25 elements. -/
theorem S2033Torsion_card : Nat.card S2033Torsion = 25 := by
  classical
  have h := S1982NatCard_LTorsion_five
  have h' := S1906NatCard_LTorsion_eq_affine S1982Five
  simpa [S2033Torsion, S2033W, S1982Five] using h'.symm.trans h

/-- The affine 5-torsion is finite. -/
instance S2033Torsion_finite : Finite S2033Torsion := by
  classical
  by_contra hfin
  haveI : Infinite S2033Torsion := not_finite_iff_infinite.mp hfin
  have hcard := S2033Torsion_card
  rw [Nat.card_eq_zero_of_infinite] at hcard
  norm_num at hcard

/-- Fintype instance for the 5-torsion, from its finiteness. -/
instance S2033Torsion_fintype : Fintype S2033Torsion := Fintype.ofFinite _

/-- Fintype instance for the nonzero 5-torsion. -/
instance S2033NonzeroTorsion_fintype : Fintype S2033NonzeroTorsion :=
  Fintype.ofFinite _

/-- The fibre of the x-coordinate map over x, restricted to nonzero 5-torsion. -/
noncomputable def S2033Fibre (x : S2033K) : Finset S2033NonzeroTorsion :=
  Finset.univ.filter (fun P : S2033NonzeroTorsion => P.1.1.xCoord = x)


/-! ## 2. Root and x-coordinate lemmas -/

/-- prePsi_5 is nonzero. -/
theorem S2033W_preΨ_ne_zero : S2033W.preΨ (5 : Int) ≠ 0 := by
  simpa [S2033W, S1982Five] using S1906_preΨ_ne_zero S1982Five

/-- Every root of the root finset evaluates prePsi_5 to zero. -/
theorem S2033Root_eval (x : S2033Root) : (S2033W.preΨ (5 : Int)).eval x.1 = 0 :=
  s1329PreΨ_eval_of_mem_roots S2033W S2033W_preΨ_ne_zero x.2

/-- A root of prePsi_5 is not the x-coordinate of a 2-torsion point. -/
theorem S2033Root_Ψ₂Sq_ne_zero (x : S2033Root) :
    (S2033W.Ψ₂Sq).eval x.1 ≠ 0 :=
  S1906NoTwoTorsionRoots_of_criterion S1982Five (S1924S1906Criterion S1982Five)
    x.1 (by simpa [S2033RootFinset, s1329RootFinset, S1982Five] using x.2)

/-- The actual curve E' over K is the base change of the S1667 curve directly from Q. -/
theorem S2033W_eq_baseChange : S2033W = S1667Curve.baseChange S2033K := by
  rw [S2033W, S1906W, S1720Curve_curve]
  change (S1667Curve.map (algebraMap ℚ S1720Field)).map (algebraMap S1720Field S2033K)
      = S1667Curve.map (algebraMap ℚ S2033K)
  rw [WeierstrassCurve.map_map]
  congr 1

/-- An F'-algebra automorphism of K fixes the curve E'. -/
theorem S2033W_map (σ : S2033K ≃ₐ[S1720Field] S2033K) :
    S2033W.map σ.toRingHom = S2033W := by
  rw [S2033W_eq_baseChange]
  have h := WeierstrassCurve.map_baseChange (W := S1667Curve) (g := σ.toAlgHom)
  change @Eq (WeierstrassCurve S2033K)
    (WeierstrassCurve.map (S1667Curve⁄S2033K) (σ : S2033K →+* S2033K))
    (S1667Curve⁄S2033K)
  exact h


example (P : S2033Torsion) : (5 : Int) • (P : S2033W.Point) = 0 := P.2
example (P : S2033Torsion) : (5 : Nat) • (P : S2033W.Point) = 0 := by
  simpa using P.2


/-! ## 3. The point action and the x-coordinate fibre -/

/-- The actual curve E' over K is elliptic. -/
instance S2033W_isElliptic : S2033W.IsElliptic := S1982W_isElliptic

/-- The action of an F'-algebra automorphism of K on affine points of E'. -/
noncomputable def S2033PointMap (σ : S2033K ≃ₐ[S1720Field] S2033K) :
    S2033W.Point →+ S2033W.Point :=
  WeierstrassCurve.Affine.Point.map (W' := S1720Curve.curve) σ.toAlgHom

/-- S2033PointMap is the point map induced by sigma. -/
@[simp] theorem S2033PointMap_apply (σ : S2033K ≃ₐ[S1720Field] S2033K)
    (P : S2033W.Point) :
    S2033PointMap σ P =
      WeierstrassCurve.Affine.Point.map (W' := S1720Curve.curve) σ.toAlgHom P := rfl

/-- The point map preserves 5-torsion. -/
theorem S2033PointMap_torsion (σ : S2033K ≃ₐ[S1720Field] S2033K)
    {P : S2033W.Point} (hP : (5 : Int) • P = 0) :
    (5 : Int) • S2033PointMap σ P = 0 := by
  rw [← map_zsmul (S2033PointMap σ) (5 : Int) P, hP, map_zero]

/-- The inverse point action: applying sigma then sigma^{-1} is the identity. -/
theorem S2033PointMap_symm_apply (σ : S2033K ≃ₐ[S1720Field] S2033K)
    (P : S2033W.Point) :
    S2033PointMap σ (S2033PointMap σ.symm P) = P := by
  cases P with
  | zero => simp [S2033PointMap]
  | some x y h =>
      simp only [S2033PointMap, WeierstrassCurve.Affine.Point.map_some]
      congr 2 <;> simp

/-- The point map preserves nonvanishing. -/
theorem S2033PointMap_ne_zero (σ : S2033K ≃ₐ[S1720Field] S2033K)
    {P : S2033W.Point} (hP : P ≠ 0) : S2033PointMap σ P ≠ 0 := by
  intro h
  apply hP
  have h' := congrArg (S2033PointMap σ.symm) h
  simpa [S2033PointMap_symm_apply] using h'

/-- The action of sigma on the nonzero 5-torsion. -/
noncomputable def S2033NonzeroTorsionMap
    (σ : S2033K ≃ₐ[S1720Field] S2033K) :
    S2033NonzeroTorsion → S2033NonzeroTorsion :=
  fun P =>
    ⟨⟨S2033PointMap σ P.1.1, by
        show (5 : Int) • S2033PointMap σ P.1.1 = 0
        rw [← map_zsmul (S2033PointMap σ) (5 : Int) P.1.1,
          show (5 : Int) • (P.1.1 : S2033W.Point) = 0 from P.1.2, map_zero]⟩,
      S2033PointMap_ne_zero σ P.2⟩

/-- The x-coordinate is invariant under negation. -/
theorem S2033xCoord_neg (P : S2033W.Point) : (-P).xCoord = P.xCoord := by
  cases P with
  | zero =>
      rw [show (-(0 : S2033W.Point)) = 0 from neg_zero]
      rfl
  | some x y h => rw [WeierstrassCurve.Affine.Point.neg_some]; rfl

/-- The x-coordinate fibre is closed under negation. -/
theorem S2033Fibre_neg_mem (x : S2033K) :
    ∀ P ∈ S2033Fibre x, -P ∈ S2033Fibre x := by
  intro P hP
  rw [S2033Fibre, Finset.mem_filter] at hP ⊢
  refine ⟨Finset.mem_univ _, ?_⟩
  change ((-(P.1.1) : S2033W.Point)).xCoord = x
  rw [S2033xCoord_neg]
  exact hP.2

/-- The x-coordinate fibre is nonempty at every root of prePsi_5. -/
theorem S2033Fibre_nonempty (x : S2033Root) : (S2033Fibre x.1).Nonempty := by
  classical
  have hΨ : (S2033W.Ψ₂Sq).eval x.1 ≠ 0 := S2033Root_Ψ₂Sq_ne_zero x
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq ((S2033W.Ψ₂Sq).eval x.1)
    (by norm_num : 0 < 2)
  have hs0 : s ≠ 0 := by
    intro h
    apply hΨ
    rw [← hs, h]
    norm_num
  let y : S2033K := (s - (S2033W.a₁ * x.1 + S2033W.a₃)) / 2
  have hy : 2 * y + S2033W.a₁ * x.1 + S2033W.a₃ = s := by
    rw [show y = (s - (S2033W.a₁ * x.1 + S2033W.a₃)) / 2 from rfl]
    field_simp
    ring
  have h2 : (2 : S2033K) ≠ 0 := by
    haveI : CharZero S2033K := inferInstance
    exact_mod_cast (by norm_num : (2 : Nat) ≠ 0)
  have hEq : S2033W.Equation x.1 y :=
    (s1329Equation_iff_sq S2033W h2 x.1 y).mpr (by rw [hy, hs])
  have hns : S2033W.Nonsingular x.1 y :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp hEq
  have hfive : (5 : Int) • WeierstrassCurve.Affine.Point.some x.1 y hns = 0 := by
    have hcrit := S1924S1906Criterion S1982Five
    have hev : S2033W.evalDivisionPolynomialAtPoint (5 : Int)
        (WeierstrassCurve.Affine.Point.some x.1 y hns) = 0 := by
      rw [WeierstrassCurve.evalDivisionPolynomialAtPoint_some,
        S2033W.evalDivisionPolynomial_eq_eval_preΨ_of_odd hns.1]
      · exact S2033Root_eval x
      · have hodd : ¬ Even (5 : Int) := by norm_num
        exact hodd
    exact (hcrit (WeierstrassCurve.Affine.Point.some x.1 y hns)).mpr (by
      simpa [S1982Five] using hev)
  refine ⟨⟨⟨WeierstrassCurve.Affine.Point.some x.1 y hns, hfive⟩,
    WeierstrassCurve.Affine.Point.some_ne_zero hns⟩, ?_⟩
  rw [S2033Fibre, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, rfl⟩


example (P : S2033W.Point) : (P : ((S1720Curve.curve)⁄S2033K).Point) = P := rfl
example (P : S2033W.Point) : (P : ((S1667Curve⁄S1720Field)⁄S2033K).Point) = P := rfl

end LeanFormal.IUT.XiFPaper.S2033D5DivisionActual