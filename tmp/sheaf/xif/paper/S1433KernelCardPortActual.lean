import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
Copyright (c) 2026 The IUT/ABC formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT/ABC formalization project
-/

/-!
# S1433: card_ker_mulByIntIsogeny_of_torsion_rational / _of_isAlgClosed, ported to Mathlib v4.32.2
with the S1430-S1432 layer absent

## The source

`tmp/TauCeti/TauCeti/AlgebraicGeometry/EllipticCurve/Isogeny/MulByInt/KernelCard.lean`
(Lean v4.36.0-rc1, 243 lines,
SHA256 `DBD7A638ADEDFC7630CAFA2DAC9B30E8B246E7F416510B3678D3D058731DCBE8`).

The two ported targets are

* line 153 `TauCeti.Isogeny.card_ker_mulByIntIsogeny_of_torsion_rational`:

  ```
  {hn : psiFunctionField W n ≠ 0}
    (hrat : ∀ P : (W.baseChange (AlgebraicClosure W.FunctionField)).toAffine.Point,
      n • P = 0 → P ∈ Set.range (Point.baseChange (W' := W) F (AlgebraicClosure W.FunctionField)))
    (hchar : (n : F) ≠ 0) : Nat.card (mulByIntIsogeny W hn).ker = n.natAbs ^ 2
  ```

* line 172 `TauCeti.Isogeny.card_ker_mulByIntIsogeny_of_isAlgClosed`: the same conclusion
  from `[IsAlgClosed F]` and `hchar` alone, obtained at line 175 by instantiating
  `hrat` with `WeierstrassCurve.mem_range_baseChange_of_zsmul_eq_zero_of_isAlgClosed`
  (`.../DivisionPolynomial/Torsion/AlgClosed.lean:65`).

## The S1430-S1432 layer is not available

There is no file `S1430*`, `S1431*` or `S1432*` under `tmp/sheaf`, and Mathlib v4.32.2
(`.lake/packages/mathlib`) has no `AlgebraicGeometry/EllipticCurve/Isogeny` module at all: no
`Isogeny` structure, no `mulByIntIsogeny`, no `psiFunctionField`, no `fieldPullback`, no
`Isogeny.ker`, no separable-degree theory of the function field of an isogeny, and no
`mem_ker_mulByIntIsogeny_iff`.  So this file writes the **exact first fields** of the two targets in
the tree's language, proves everything that can be proved without that layer (in particular the whole
of the second target's reduction), and records the **dependency table** of the missing layer, with the
exact source file and line of each obligation.

## API replacement

| TauCeti (Lean v4.36.0-rc1) | this file (Mathlib v4.32.2) |
| --- | --- |
| `(W⁄F).toAffine.Point`, the `F`-points of the source | `W.Point`; here `(W⁄F).Point = W.Point` by `rfl` |
| `(W.baseChange Ω).toAffine.Point`, the `Ω`-points | `(W⁄Ω).Point` |
| `(mulByIntIsogeny W hn).ker`, with `hn : psiFunctionField W n ≠ 0` | `AddSubgroup.torsionBy W.Point n`, which is the source's `ker_mulByIntIsogeny_eq_torsionBy` (`MulByInt/Kernel.lean:98`) read as a definition of the ported conclusion |
| `Point.baseChange (W' := W) F Ω` | `Point.baseChange F Ω`, abbreviated `toAlgClosure` at `Ω = AlgebraicClosure F` |
| `hrat`, rationality over `AlgebraicClosure W.FunctionField` | `S1433TorsionRational W n`, the same condition at `Ω = AlgebraicClosure F` |
| `hn : psiFunctionField W n ≠ 0` | dropped: in the source it only excludes `n = 0` (`ne_zero_of_psiFunctionField_ne_zero`, line 93) |
| `hchar : (n : F) ≠ 0` | kept unchanged, as the hypothesis of the source-shaped statements |

Two exact type differences are recorded, not hidden.

* The source counts `ker [n]`, a subgroup of `(W⁄F).Point` defined as the group of translations
  fixing the pulled-back function field (`Isogeny/Kernel.lean:75`).  Mathlib has no isogeny, so the
  count is written on `AddSubgroup.torsionBy W.Point n`, which is where the source's own
  `natCard_torsionBy_of_torsion_rational` (line 188) lands.  The identification of the two is the
  source's `ker_mulByIntIsogeny_eq_torsionBy`, i.e. an S1430 obligation; it is not assumed here, it
  is simply not needed to *state* the ported conclusion.
* The source's rationality hypothesis lives over `AlgebraicClosure W.FunctionField`, the algebraic
  closure of the function field, because `Field.Emb K L` lands in `AlgebraicClosure K`.  The
  ported count is a count of `W.Point`, so the rationality it needs is rationality over
  `AlgebraicClosure F`, and that is the shape written here.

## What is proved here (no sorry, no axiom, no added hypothesis standing in for a proof)

1. `toAlgClosure`, `toAlgClosure_injective`, `toAlgClosure_surjective` and
   `toAlgClosure_bijective`: base change of points along `F → AlgebraicClosure F` is bijective as
   soon as `F` is algebraically closed, because `algebraMap F (AlgebraicClosure F)` is bijective
   (`IsAlgClosed.algebraMap_bijective_of_isIntegral`, `AlgebraicClosure F` being integral over
   `F`).
2. `S1433TorsionRational`, the rationality **first field**, and
   `s1433TorsionRational_of_isAlgClosed`: over an algebraically closed base it holds, so the source's
   `[IsAlgClosed F]` route through `mem_range_baseChange_of_zsmul_eq_zero_of_isAlgClosed` is
   closed here.
3. `torsionSubtypeEquiv` and `natCard_torsionBy_eq_of_torsionRational`: rationality makes the
   rational `n`-torsion *all* of the geometric `n`-torsion, as an `Equiv` and hence as a
   `Nat.card` equality.  This is the ported content of the source's
   `card_emb_mulByIntIsogeny_le_card_ker` (line 116) at the level of points.
4. `S1433KernelCard`, the **conclusion first field**
   `Nat.card (AddSubgroup.torsionBy W.Point n) = n.natAbs ^ 2`, and
   `S1433GeometricTorsionCard`, the **geometric-count first field** which is where the missing
   S1430/S1431 work lands.
5. `s1433KernelCard_of_torsionRational_of_geometricTorsionCard`: rationality plus the geometric
   count give the ported `of_torsion_rational` conclusion.  Neither side is restated as the other,
   and the rationality input is discharged by item 1 in the closure case.
6. `s1433KernelCard_of_isAlgClosed_of_torsionRationalTheorem`: the source's second theorem from its
   first, using item 2 for the instantiation of `hrat`.  This is precisely the source's derivation at
   line 175, so after this file the second target has no gap of its own: it inherits exactly the gap of
   the first.
7. `S1433PortLayer`, `S1433PortDep` and `s1433Deps`: the dependency table, with the exact
   source file and line of every obligation this file does not prove.
8. `s1433KernelCard_one`, `s1433KernelCard_neg_one`: the conclusion first field is inhabited at
   `n = ±1`, so it is not vacuous.

## Not proved here

* `S1433GeometricTorsionCard W n` for `n` invertible in `F`, i.e. `#E[n] = n ^ 2` over an
  algebraically closed field.  In the source this is `#ker [n] ≤ sepDeg [n] = n ^ 2` together with
  `sepDeg [n] ≤ #ker [n]`, using `card_ker_le_separableDegree` and
  `separableDegree_mulByIntIsogeny` (S1431) for the upper end and
  `card_emb_mulByIntIsogeny_le_card_ker` (S1432) for the lower end.  None of those three exists here,
  and none is assumed in its place: the count is a named `Prop`, used only as an explicit hypothesis
  of the reduction.
* `S1433TorsionRational W n` for a field that is not algebraically closed, and for the source's
  `Ω = AlgebraicClosure W.FunctionField` rather than `AlgebraicClosure F`; the source's proof goes
  through integrality of the coordinates of a torsion point (`isIntegral_x_of_zsmul_eq_zero`,
  `mem_range_y_of_equation_of_mem_range_x`), which the `AlgebraicClosure F` case does not need.

## Dependency table (prose form; the Lean form is `s1433Deps` below)

| # | source (file:line) | layer | obligation | status |
| --- | --- | --- | --- | --- |
| 1 | `Isogeny/Basic.lean:139` | S1430 | `structure Isogeny` with `pullback` | absent |
| 2 | `MulByInt/MapsInfinity.lean:103` | S1430 | `mulByIntIsogeny W hn` for `hn : psiFunctionField W n ≠ 0` | absent |
| 3 | `FunctionField.lean:167` | S1430 | `fieldPullback` and `fieldRange` | absent |
| 4 | `MulByInt/Kernel.lean:98` | S1430 | `ker [n] = AddSubgroup.torsionBy (W⁄F).Point n` | absent; replaced by definition in the ported conclusion |
| 5 | `Isogeny/Kernel.lean:140` | S1431 | `Nat.card ker ≤ sepDeg` | absent |
| 6 | `Isogeny/Separability.lean:101` | S1431 | `separableDegree = Field.finSepDegree φ.fieldPullback.fieldRange W₁.FunctionField` | absent |
| 7 | `MulByInt/Separability.lean:71` | S1431 | `sepDeg [n] = n.natAbs ^ 2` from `hchar : (n : F) ≠ 0` | absent; the only consumer of `hchar` |
| 8 | `KernelCard.lean:77` | S1432 | `zsmul_map_sub_map_genericPoint_eq_zero` | absent |
| 9 | `KernelCard.lean:102` | S1432 | `mem_range_baseChange_sub_map_genericPoint_mulByInt` | absent |
| 10 | `KernelCard.lean:116` | S1432 | `Nat.card (Field.Emb L W.FunctionField) ≤ Nat.card ker` | absent |
| 11 | `DivisionPolynomial/Torsion/AlgClosed.lean:65` | S1432 | geometric torsion is rational over an algebraically closed base | **proved here**, `s1433TorsionRational_of_isAlgClosed` (stronger: all points, no `n ≠ 0`) |
| 12 | `KernelCard.lean:153` | target | `#ker [n] = n ^ 2` from `hrat` and `hchar` | ported shape `S1433TorsionRationalTheorem`; conclusion `S1433KernelCard`, not proved |
| 13 | `KernelCard.lean:172` | target | the same over `[IsAlgClosed F]` | **reduced here** to #12, not proved |
| 14 | `KernelCard.lean:188` | consumer | the count read on `AddSubgroup.torsionBy` | identical to `S1433KernelCard` |
| 15 | `KernelCard.lean:200` | consumer | `Finite (E[n])` for `n ≠ 0` | not repeated here; ported as `finite_torsionBy_of_torsionCardinalityAt` in `S1395TorsionCardinalityPortActual.lean` |

## Status

`statement_compiles`: yes (`lake env lean`, exit 0).
`proof_body_checked`: yes for items 1-8 of the list above.
`kernel_closed`: only for items 1-8; `S1433GeometricTorsionCard` is a named unproved input and
`S1433KernelCard` is not proved.
`target_accepted`: no.  Both source targets stay open at the geometric count; this file is the exact
first fields, the exact reduction, and the exact dependency table.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.S1433KernelCardPortActual

open WeierstrassCurve WeierstrassCurve.Affine

universe u

variable {F : Type u} [Field F] [DecidableEq F]

/-- `AlgebraicClosure F` is a field, so classical decidable equality suffices for its points. -/
local instance instDecidableEqAlgebraicClosure : DecidableEq (AlgebraicClosure F) :=
  Classical.decEq _

/-! ## 1. Points over the algebraic closure: base change is bijective -/

/-- The rational points of `W` inside its points over the algebraic closure, i.e. the base change
`W.Point → (W⁄(AlgebraicClosure F)).Point` along `F → AlgebraicClosure F`.  This is the ported
`Point.baseChange (W' := W) F (AlgebraicClosure -)` of the source. -/
def toAlgClosure (W : WeierstrassCurve.Affine F) :
    W.Point →+ (W⁄(AlgebraicClosure F)).Point :=
  Point.baseChange (W' := W) F (AlgebraicClosure F)

/-- Base change along `F → AlgebraicClosure F` is injective, being induced by an injective field
map. -/
theorem toAlgClosure_injective (W : WeierstrassCurve.Affine F) :
    Function.Injective (toAlgClosure W) := by
  have h : toAlgClosure W = Point.map (W' := W) (Algebra.ofId F (AlgebraicClosure F)) := rfl
  rw [h]
  exact Point.map_injective _

/-- Base change of a nonsingular affine point: the coordinates are mapped and the nonsingularity
proof is carried along, the two proofs being propositionally equal. -/
theorem toAlgClosure_some (W : WeierstrassCurve.Affine F) {x y : F} (h : W.Nonsingular x y)
    (h' : (W⁄(AlgebraicClosure F)).Nonsingular (algebraMap F (AlgebraicClosure F) x)
      (algebraMap F (AlgebraicClosure F) y)) :
    toAlgClosure W (Point.some x y h) =
      Point.some (algebraMap F (AlgebraicClosure F) x) (algebraMap F (AlgebraicClosure F) y) h' :=
  rfl

/-- **Base change along `F → AlgebraicClosure F` is surjective when `F` is algebraically
closed**: `algebraMap F (AlgebraicClosure F)` is bijective because `AlgebraicClosure F` is
integral over the algebraically closed `F`, and the equation and nonsingularity transfer through
that bijection.  This is the ported
`WeierstrassCurve.mem_range_baseChange_of_zsmul_eq_zero_of_isAlgClosed`
(`DivisionPolynomial/Torsion/AlgClosed.lean:65`) at `Ω = AlgebraicClosure F`, with the torsion
hypothesis dropped: over the algebraic closure of the base every point is rational, not only the
torsion points. -/
theorem toAlgClosure_surjective [IsAlgClosed F] (W : WeierstrassCurve.Affine F) :
    Function.Surjective (toAlgClosure W) := by
  have hbij : Function.Bijective (algebraMap F (AlgebraicClosure F)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  intro P
  rcases P with _ | ⟨x, y, hns⟩
  · exact ⟨0, map_zero _⟩
  · obtain ⟨x₀, hx₀⟩ : ∃ x₀ : F, algebraMap F (AlgebraicClosure F) x₀ = x := hbij.2 x
    obtain ⟨y₀, hy₀⟩ : ∃ y₀ : F, algebraMap F (AlgebraicClosure F) y₀ = y := hbij.2 y
    subst hx₀
    subst hy₀
    obtain hns₀ : W.Nonsingular x₀ y₀ :=
      (baseChange_nonsingular (W := W) (f := Algebra.ofId F (AlgebraicClosure F)) hbij.1
        x₀ y₀).mp hns
    exact ⟨Point.some x₀ y₀ hns₀, toAlgClosure_some W hns₀ hns⟩

/-- Base change along `F → AlgebraicClosure F` is bijective when `F` is algebraically closed. -/
theorem toAlgClosure_bijective [IsAlgClosed F] (W : WeierstrassCurve.Affine F) :
    Function.Bijective (toAlgClosure W) :=
  ⟨toAlgClosure_injective W, toAlgClosure_surjective W⟩

/-! ## 2. The rationality first field -/

/-- **The rationality first field**: every geometric `n`-torsion point of `W` is the base change of a
rational one.  This is the hypothesis `hrat` of `card_ker_mulByIntIsogeny_of_torsion_rational`
(`MulByInt/KernelCard.lean:154`), read at `Ω = AlgebraicClosure F`, which is the closure the
ported count needs; the source reads it at `Ω = AlgebraicClosure W.FunctionField` because its
embeddings land there. -/
def S1433TorsionRational (W : WeierstrassCurve.Affine F) (n : ℤ) : Prop :=
  ∀ P : (W⁄(AlgebraicClosure F)).Point, n • P = 0 → P ∈ Set.range (toAlgClosure W)

/-- **The rationality first field holds over an algebraically closed base**: nothing in the algebraic
closure of an algebraically closed field is new, so the torsion rationality the source extracts from
`[IsAlgClosed F]` is available here outright. -/
theorem s1433TorsionRational_of_isAlgClosed [IsAlgClosed F]
    (W : WeierstrassCurve.Affine F) (n : ℤ) : S1433TorsionRational W n :=
  fun P _ => toAlgClosure_surjective W P

/-! ## 3. Rationality identifies the geometric torsion with the rational torsion -/

/-- **Under rationality the rational `n`-torsion is all the geometric `n`-torsion**, as an
equivalence of the two torsion subtypes.  This is the point-level content of the source's
`card_emb_mulByIntIsogeny_le_card_ker` (`KernelCard.lean:116`), where the embedding count is
bounded by the kernel: here the kernel is `torsionBy` and the bound becomes an equality of
cardinalities. -/
def torsionSubtypeEquiv (W : WeierstrassCurve.Affine F) (n : ℤ)
    (h : S1433TorsionRational W n) :
    {P : W.Point // n • P = 0} ≃ {P : (W⁄(AlgebraicClosure F)).Point // n • P = 0} where
  toFun P := ⟨toAlgClosure W P.1, by rw [← map_zsmul, P.2, map_zero]⟩
  invFun P :=
    ⟨Classical.choose (h P.1 P.2), by
      refine toAlgClosure_injective W ?_
      rw [map_zsmul, Classical.choose_spec (h P.1 P.2), P.2, map_zero]⟩
  left_inv P := by
    have hP : n • toAlgClosure W P.1 = 0 := by rw [← map_zsmul, P.2, map_zero]
    exact Subtype.ext
      (toAlgClosure_injective W (Classical.choose_spec (h (toAlgClosure W P.1) hP)))
  right_inv P := Subtype.ext (Classical.choose_spec (h P.1 P.2))

/-- **Rationality gives the cardinality of the geometric torsion**: the rational `n`-torsion
subgroup and the geometric one have the same number of points. -/
theorem natCard_torsionBy_eq_of_torsionRational (W : WeierstrassCurve.Affine F) (n : ℤ)
    (h : S1433TorsionRational W n) :
    Nat.card (AddSubgroup.torsionBy W.Point n) =
      Nat.card (AddSubgroup.torsionBy (W⁄(AlgebraicClosure F)).Point n) := by
  have h₁ : Nat.card (AddSubgroup.torsionBy W.Point n) =
      Nat.card {P : W.Point // n • P = 0} := rfl
  have h₂ : Nat.card (AddSubgroup.torsionBy (W⁄(AlgebraicClosure F)).Point n) =
      Nat.card {P : (W⁄(AlgebraicClosure F)).Point // n • P = 0} := rfl
  rw [h₁, h₂]
  exact Nat.card_congr (torsionSubtypeEquiv W n h)

/-! ## 4. The two first fields and the reduction -/

/-- **The conclusion first field**: the ported conclusion of
`card_ker_mulByIntIsogeny_of_torsion_rational`, i.e. `#ker [n] = n ^ 2` read on Mathlib's
intrinsic torsion subgroup (`ker_mulByIntIsogeny_eq_torsionBy`, `MulByInt/Kernel.lean:98`).  This
is the same statement as `TorsionCardinalityAt` in `S1395TorsionCardinalityPortActual.lean`;
it is restated here so that this file is standalone, and the two must be kept identical. -/
def S1433KernelCard (W : WeierstrassCurve.Affine F) (n : ℤ) : Prop :=
  Nat.card (AddSubgroup.torsionBy W.Point n) = n.natAbs ^ 2

/-- **The geometric-count first field**: `#E[n] = n ^ 2` over the algebraic closure.  This is where
the S1430-S1432 layer lands: the source derives it from `#ker [n] ≤ sepDeg [n] ≤ #ker [n]` and
`sepDeg [n] = n ^ 2`.  It is a named input here, not a hypothesis of a different shape. -/
def S1433GeometricTorsionCard (W : WeierstrassCurve.Affine F) (n : ℤ) : Prop :=
  Nat.card (AddSubgroup.torsionBy (W⁄(AlgebraicClosure F)).Point n) = n.natAbs ^ 2

/-- **The ported `card_ker_mulByIntIsogeny_of_torsion_rational` from rationality and the geometric
count.**  The two inputs are exactly the two halves of the source's `le_antisymm`: rationality
identifies the rational count with the geometric one (third section), and the geometric count is
`sepDeg [n] = n ^ 2` combined with the kernel bound. -/
theorem s1433KernelCard_of_torsionRational_of_geometricTorsionCard
    {W : WeierstrassCurve.Affine F} {n : ℤ}
    (hrat : S1433TorsionRational W n) (hgeo : S1433GeometricTorsionCard W n) :
    S1433KernelCard W n := by
  unfold S1433KernelCard
  rw [natCard_torsionBy_eq_of_torsionRational W n hrat]
  exact hgeo

/-- **The source's two theorems at the algebraic closure**: over an algebraically closed base the
rationality input is discharged, so the only input left is the geometric count. -/
theorem s1433KernelCard_of_isAlgClosed_of_geometricTorsionCard [IsAlgClosed F]
    {W : WeierstrassCurve.Affine F} {n : ℤ}
    (hgeo : S1433GeometricTorsionCard W n) : S1433KernelCard W n :=
  s1433KernelCard_of_torsionRational_of_geometricTorsionCard
    (s1433TorsionRational_of_isAlgClosed W n) hgeo

/-! ## 5. The source's theorem shapes -/

/-- The exact shape of the source's `card_ker_mulByIntIsogeny_of_torsion_rational` at the
`torsionBy` conclusion: rationality and `(n : F) ≠ 0` give `#ker [n] = n ^ 2`.  The index
hypothesis `hn : psiFunctionField W n ≠ 0` of the source is dropped, as it only excludes
`n = 0`. -/
def S1433TorsionRationalTheorem (W : WeierstrassCurve.Affine F) [W.IsElliptic] (n : ℤ) : Prop :=
  S1433TorsionRational W n → (n : F) ≠ 0 → S1433KernelCard W n

/-- **The source's `card_ker_mulByIntIsogeny_of_isAlgClosed` from its
`card_ker_mulByIntIsogeny_of_torsion_rational`**: the closure assumption is used at
`KernelCard.lean:176` only to supply `hrat` through
`mem_range_baseChange_of_zsmul_eq_zero_of_isAlgClosed`, and that supply is proved in this file
(`s1433TorsionRational_of_isAlgClosed`).  So the second target has no gap beyond the first. -/
theorem s1433KernelCard_of_isAlgClosed_of_torsionRationalTheorem [IsAlgClosed F]
    {W : WeierstrassCurve.Affine F} [W.IsElliptic] {n : ℤ}
    (h : S1433TorsionRationalTheorem W n) (hchar : (n : F) ≠ 0) : S1433KernelCard W n :=
  h (s1433TorsionRational_of_isAlgClosed W n) hchar

/-! ## 6. The conclusion first field is not vacuous -/

/-- The `n = 1` instance of the conclusion first field: the `1`-torsion subgroup is trivial. -/
theorem s1433KernelCard_one (W : WeierstrassCurve.Affine F) : S1433KernelCard W (1 : ℤ) := by
  have hbot : AddSubgroup.torsionBy W.Point (1 : ℤ) = ⊥ := by
    show (Submodule.torsionBy ℤ W.Point (1 : ℤ)).toAddSubgroup = ⊥
    rw [Submodule.torsionBy_one]
    rfl
  unfold S1433KernelCard
  rw [hbot, Nat.card_unique]
  norm_num

/-- The `n = -1` instance of the conclusion first field. -/
theorem s1433KernelCard_neg_one (W : WeierstrassCurve.Affine F) : S1433KernelCard W (-1 : ℤ) := by
  have h1 : S1433KernelCard W (1 : ℤ) := s1433KernelCard_one W
  unfold S1433KernelCard at h1 ⊢
  rw [AddSubgroup.torsionBy.neg, h1]
  norm_num

/-! ## 7. The dependency table -/

/-- The three layers the source's proof needs beyond this file. -/
inductive S1433PortLayer where
  /-- The multiplication-by-`n` isogeny, its function-field pullback and its kernel. -/
  | s1430
  /-- The separable degree: `#ker ≤ sepDeg` and `sepDeg [n] = n ^ 2`. -/
  | s1431
  /-- The generic point, the embedding count and the rationality of geometric torsion. -/
  | s1432
  deriving DecidableEq, Repr

/-- One row of the dependency table: the source declaration, the layer that must supply its port,
the ported obligation, and its status in this tree. -/
structure S1433PortDep where
  /-- The source declaration as `file:line`, relative to
  `tmp/TauCeti/TauCeti/AlgebraicGeometry/EllipticCurve`. -/
  source : String
  /-- The layer that must supply it. -/
  layer : S1433PortLayer
  /-- The ported obligation. -/
  obligation : String
  /-- Its status here. -/
  status : String
  deriving Repr

/-- **The dependency table of S1433**, in the order the source's proof uses it. -/
def s1433Deps : List S1433PortDep := [
  ⟨"Isogeny/Basic.lean:139", .s1430, "structure Isogeny with pullback",
    "absent: Mathlib v4.32.2 has no Isogeny module"⟩,
  ⟨"MulByInt/MapsInfinity.lean:103", .s1430,
    "mulByIntIsogeny W hn for hn : psiFunctionField W n ≠ 0", "absent"⟩,
  ⟨"FunctionField.lean:167", .s1430, "fieldPullback and fieldRange", "absent"⟩,
  ⟨"MulByInt/Kernel.lean:98", .s1430,
    "ker [n] = AddSubgroup.torsionBy (W⁄F).Point n",
    "absent; replaced by definition in S1433KernelCard"⟩,
  ⟨"Isogeny/Kernel.lean:140", .s1431, "Nat.card ker ≤ sepDeg", "absent"⟩,
  ⟨"Isogeny/Separability.lean:101", .s1431,
    "separableDegree = Field.finSepDegree φ.fieldPullback.fieldRange W₁.FunctionField", "absent"⟩,
  ⟨"MulByInt/Separability.lean:71", .s1431,
    "sepDeg [n] = n.natAbs ^ 2 from (n : F) ≠ 0",
    "absent; the only consumer of hchar"⟩,
  ⟨"KernelCard.lean:77", .s1432, "zsmul_map_sub_map_genericPoint_eq_zero", "absent"⟩,
  ⟨"KernelCard.lean:102", .s1432,
    "mem_range_baseChange_sub_map_genericPoint_mulByInt", "absent"⟩,
  ⟨"KernelCard.lean:116", .s1432,
    "Nat.card (Field.Emb L W.FunctionField) ≤ Nat.card ker", "absent"⟩,
  ⟨"DivisionPolynomial/Torsion/AlgClosed.lean:65", .s1432,
    "geometric torsion is rational over an algebraically closed base",
    "proved here: s1433TorsionRational_of_isAlgClosed (all points, no n ≠ 0)"⟩,
  ⟨"KernelCard.lean:153", .s1430,
    "ker [n] = n ^ 2 from hrat and hchar",
    "ported shape S1433TorsionRationalTheorem; not proved"⟩,
  ⟨"KernelCard.lean:172", .s1432, "ker [n] = n ^ 2 over [IsAlgClosed F]",
    "reduced here to line 153; not proved"⟩,
  ⟨"KernelCard.lean:188", .s1430, "Nat.card (torsionBy _ n) = n.natAbs ^ 2",
    "identical to S1433KernelCard"⟩,
  ⟨"KernelCard.lean:200", .s1430, "Finite (torsionBy _ n) for n ≠ 0",
    "ported in S1395TorsionCardinalityPortActual.lean, not repeated"⟩]

/-- The table has all fifteen rows listed in the module documentation. -/
theorem s1433Deps_length : s1433Deps.length = 15 := rfl

/-! ## 8. Axiom footprint -/

#print axioms toAlgClosure_injective
#print axioms toAlgClosure_surjective
#print axioms toAlgClosure_bijective
#print axioms s1433TorsionRational_of_isAlgClosed
#print axioms natCard_torsionBy_eq_of_torsionRational
#print axioms s1433KernelCard_of_torsionRational_of_geometricTorsionCard
#print axioms s1433KernelCard_of_isAlgClosed_of_geometricTorsionCard
#print axioms s1433KernelCard_of_isAlgClosed_of_torsionRationalTheorem
#print axioms s1433KernelCard_one
#print axioms s1433KernelCard_neg_one
#print axioms s1433Deps_length

end LeanFormal.IUT.XiFPaper.S1433KernelCardPortActual
