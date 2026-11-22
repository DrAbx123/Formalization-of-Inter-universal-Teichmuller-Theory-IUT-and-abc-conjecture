import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.Algebra.Module.Torsion.Basic

/-!
# S1395: the D5 torsion cardinality `#E[n] = n ^ 2`, Mathlib-only port

## The ported target

D5 (the torsion clause of Definition 3.1) needs exactly one cardinality: for a prime
`l >= 5` and an elliptic curve `W` over a field `F` in which `l` is invertible,

  `Nat.card (W.Point[l]) = l ^ 2`,

together with its fiber form: a nonempty `[l]`-fiber is a coset of `W.Point[l]`, so it also
has `l ^ 2` points.  TauCeti proves this as

* `TauCeti.Isogeny.card_zsmul_fiber_eq_card_ker`
  (`tmp/TauCeti/TauCeti/AlgebraicGeometry/EllipticCurve/Isogeny/MulByInt/Fiber.lean:46`),
* `TauCeti.Isogeny.card_zsmul_fiber` (same file, line 56),
* `TauCeti.Isogeny.card_ker_mulByIntIsogeny_of_torsion_rational`
  (`.../MulByInt/KernelCard.lean:153`),
* `WeierstrassCurve.Affine.natCard_torsionBy_of_torsion_rational`
  (`.../MulByInt/KernelCard.lean:188`),
* `WeierstrassCurve.Affine.finite_torsionBy` (`.../MulByInt/KernelCard.lean:200`),
* `TauCeti.Isogeny.card_ker_mulByPrimeIsogeny_of_torsion_rational`
  (`.../MulByInt/KernelCard.lean:232`).

This file ports that chain to the Mathlib available at this checkout
(`Mathlib` pinned at `v4.32.2`, `D:\lean\.lake\packages\mathlib`) as far as Mathlib
allows, and names the exact first field where it stops.

## API replacement

| TauCeti | Mathlib (this file) |
| --- | --- |
| `(W⁄F).toAffine.Point` | `W.Point` |
| `TauCeti.Isogeny.mulByIntIsogeny W hn` with kernel `Isogeny.ker` | `AddSubgroup.torsionBy W.Point n` (`Mathlib.Algebra.Module.Torsion.Basic`; its carrier is literally `{x // n • x = 0}`, so no kernel identification is needed) |
| `TauCeti.Isogeny.mem_ker_mulByIntIsogeny_iff` | definitional: `x ∈ torsionBy W.Point n ↔ n • x = 0` (`Submodule.mem_torsionBy_iff`) |
| `TauCeti.GroupTheory.Coset.Fiber.card_zsmul_fiber_eq_card_zsmul_eq_zero` | the explicit translation equivalence `P ↦ P - P₀` below (`natCard_zsmulFiber_eq_natCard_torsionBy`), proved here |
| `psiFunctionField W n ≠ 0` | dropped: in TauCeti it only rules out `n = 0` (`ne_zero_of_psiFunctionField_ne_zero`); the Mathlib statement has no division function |
| `[IsAlgClosed F]`, `(n : F) ≠ 0`, and the rationality hypothesis `hrat` | the *proof inputs* of the first field; they are not hypotheses of the reduction below, because they are used in TauCeti only to prove the first field |
| `Nat.card`, `Nat.card_congr`, `zsmul_sub`, `zsmul_add` | unchanged |

Two exact type differences are recorded, not hidden:

* Mathlib has `WeierstrassCurve.Affine.baseChange` and `Affine.Point.map`, but no
  `baseChange_self`, so the trivial base change `W⁄F` of the source is not definitionally
  `W`.  The port is therefore stated on `W.Point` and never on `(W⁄F).Point`.
* TauCeti's `Isogeny.ker` is a subtype of `(W⁄F).Point`; Mathlib's `AddSubgroup.torsionBy`
  is a subgroup of `W.Point`.  The two are compared by cardinality only through the
  group-theoretic translation below, which is where the `ker = E[n]` identification of the
  source is replaced by the definition of `torsionBy`.

## What is proved here, and the exact boundary

Proved, with no `sorry`, no `axiom`, no added hypothesis in place of a proof:

1. `zsmulFiber` and `natCard_zsmulFiber_eq_natCard_torsionBy`: for an arbitrary additive
   commutative group `A`, a nonempty `[n]`-fiber has the cardinality of `A[n]`.  This is the
   port of `card_zsmul_fiber_eq_card_ker`, and it is where the coset count lives in Mathlib
   (`AddSubgroup.torsionBy` is a subgroup, so `P - P₀` is an `Equiv` onto it).
2. `natCard_zsmul_fiber_eq_card_torsionBy`: the same statement on `W.Point` for a
   Weierstrass curve `W`.
3. `TorsionCardinalityAt W n`, the **exact first field**:
   `Nat.card (AddSubgroup.torsionBy W.Point n) = n.natAbs ^ 2`.
4. `card_zsmul_fiber`: the ported `TauCeti.Isogeny.card_zsmul_fiber`, *from* the first
   field.
5. `torsionCardinalityAt_iff_card_fiber`: the first field is *equivalent* to the family of
   fiber counts of the ported `card_zsmul_fiber`, so the reduction loses nothing: the fiber
   form holds for every nonempty `[n]`-fiber exactly when the first field holds.
6. `finite_torsionBy_of_torsionCardinalityAt`: the first field at `n ≠ 0` gives finiteness of
   `W.Point[n]`, the port of `WeierstrassCurve.Affine.finite_torsionBy` at that input.
7. `card_zsmul_fiber_prime` and `natCard_torsionBy_prime`: the `l ^ 2` forms, which is the
   shape D5 (`l` prime, `l >= 5`) consumes.
8. `torsionCardinalityAt_one`, `torsionCardinalityAt_neg_one`: the first field is
   inhabited at `n = ±1`, so it is not vacuous.

Not proved here: `TorsionCardinalityAt W n` for a general `n` with `(n : F) ≠ 0`.

Why the source proof cannot be replayed against Mathlib.  TauCeti obtains the first field
as `#ker [n] = n.natAbs ^ 2`, by

* `card_ker_le_separableDegree`, i.e. `#ker [n] <= sepDeg [n]`,
* `separableDegree_mulByIntIsogeny W hchar`, i.e. `sepDeg [n] = n ^ 2` for `n` invertible,
* `card_emb_mulByIntIsogeny_le_card_ker`, i.e. `sepDeg [n] <= #ker [n]` from rationality:
  embeddings of the function field `K(W)` over the pulled-back field
  `(mulByIntIsogeny W hn).fieldPullback.fieldRange` are injective into `ker [n]`, since two
  embeddings that agree there move the generic point by an `n`-torsion difference
  (`zsmul_map_sub_map_genericPoint_eq_zero`).

Every one of these objects is absent from this Mathlib: there is no multiplication-by-`n`
isogeny on `W.Point` (`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean` has the
group law and `Point.map` for algebra maps, but no `[n]`, no `Isogeny`, no degree, no
separable degree), no `fieldPullback` and no theory of separable degree of function-field
extensions of curves (`W.FunctionField` exists, and `W.ψ`, `W.Ψ`, `W.ΨSq`, `W.Φ` exist with
degree results such as `natDegree_Φ n = n.natAbs ^ 2` and `coeff_ΨSq n = n ^ 2`, but no lemma
connects these division polynomials to `W.Point` or to torsion), and no rationality lemma of
the form `mem_range_baseChange_of_zsmul_eq_zero_of_isAlgClosed`.  Replaying the source proof
would therefore mean vendoring the whole TauCeti isogeny/function-field closure; the task is
to port this one cardinality, and it is not vendored.  The first field named above is
`card_ker_mulByIntIsogeny_of_torsion_rational`'s conclusion on Mathlib's `torsionBy`; it is
the exact theorem Mathlib is missing, and nothing weaker is substituted for it.

## Relation to the tree's D5 input

The same shape is already consumed at the concrete Gaussian curve inside the tree:
`S1366TorsionCardinality l` (`tmp/sheaf/xif/paper/S1366PrePsiSeparabilityFix.lean:209`) is
`Nat.card (S1298TorsionCarrier l) = l.value ^ 2`, and
`s1366ExistsTorsionFinset_of_cardinality` converts it to the affine form
`Nat.card (AddSubgroup.torsionBy (S1329Curve l).Point (l.value : ℤ)) = l.value ^ 2`, which is
exactly `natCard_torsionBy_prime` at `W = S1329Curve l`.  This file does not import
S1298/S1329/S1366: the port stays at the Mathlib level, and the identification of
`S1298TorsionCarrier l` with `(S1329Curve l).Point` stays where it was
(`s1329NatCard_carrier_eq`, in S1329, outside this file).  The other S1366 input,
`S1366TorsionDetection l`, is the division-polynomial-to-torsion link that this Mathlib also
lacks, and it is not re-proved or assumed here.

## Status

`statement_compiles`: yes (this file is checked by `lake env lean`, exit 0).
`proof_body_checked`: yes for items 1-8.
`kernel_closed`: only for items 1-8; `TorsionCardinalityAt` is a named unproved input.
`target_accepted`: no.  D5 stays open at `TorsionCardinalityAt`; this file is the exact
reduction plus the exact first field, not a proof of `#E[n] = n ^ 2`.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S1395TorsionCardinalityPortActual

open WeierstrassCurve

universe u

/-! ## 1. The coset count in an additive commutative group -/

section AddCommGroup

variable {A : Type*} [AddCommGroup A]

/-- The `[n]`-fiber over `T`: the points carried to `T` by multiplication by `n`. -/
def zsmulFiber (n : ℤ) (T : A) : Type _ :=
  {P : A // n • P = T}

/-- **A nonempty `[n]`-fiber has as many points as the `n`-torsion subgroup.**  This is the
port of `TauCeti.Isogeny.card_zsmul_fiber_eq_card_ker`: the fiber over `T` is a torsor under
`A[n]`, and the translation `P ↦ P - P₀` is an equivalence for any `P₀` with `n • P₀ = T`. -/
theorem natCard_zsmulFiber_eq_natCard_torsionBy (n : ℤ) {T P₀ : A} (hP₀ : n • P₀ = T) :
    Nat.card (zsmulFiber n T) = Nat.card (AddSubgroup.torsionBy A n) := by
  have key : Nat.card (zsmulFiber n T) = Nat.card {Q : A // n • Q = 0} := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun P => ⟨P.1 - P₀, ?_⟩
        invFun := fun Q => ⟨Q.1 + P₀, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · show n • (P.1 - P₀) = 0
      rw [zsmul_sub, P.2, hP₀, sub_self]
    · show n • (Q.1 + P₀) = T
      rw [zsmul_add, Q.2, hP₀, zero_add]
    · intro P
      exact Subtype.ext (by simp)
    · intro Q
      exact Subtype.ext (by simp)
  have key₂ : Nat.card {Q : A // n • Q = 0} = Nat.card (AddSubgroup.torsionBy A n) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => (Submodule.mem_torsionBy_iff n x).symm)
  rw [key, key₂]

/-- The kernel form: the `[n]`-fiber over `0` has the cardinality of `A[n]`. -/
theorem natCard_zsmulFiber_zero (n : ℤ) :
    Nat.card (zsmulFiber n (0 : A)) = Nat.card (AddSubgroup.torsionBy A n) :=
  natCard_zsmulFiber_eq_natCard_torsionBy (P₀ := 0) n (by simp)

theorem natCard_torsionBy_neg (n : ℤ) :
    Nat.card (AddSubgroup.torsionBy A (-n)) = Nat.card (AddSubgroup.torsionBy A n) := by
  rw [AddSubgroup.torsionBy.neg]

theorem natCard_torsionBy_one (A : Type*) [AddCommGroup A] :
    Nat.card (AddSubgroup.torsionBy A (1 : ℤ)) = 1 := by
  have hbot : AddSubgroup.torsionBy A (1 : ℤ) = ⊥ := by
    show (Submodule.torsionBy ℤ A (1 : ℤ)).toAddSubgroup = ⊥
    rw [Submodule.torsionBy_one]
    rfl
  rw [hbot]
  exact Nat.card_unique

theorem natCard_torsionBy_neg_one (A : Type*) [AddCommGroup A] :
    Nat.card (AddSubgroup.torsionBy A (-1 : ℤ)) = 1 := by
  rw [AddSubgroup.torsionBy.neg]
  exact natCard_torsionBy_one A

end AddCommGroup

/-! ## 2. The Weierstrass-curve cardinality, on `W.Point` -/

section WeierstrassCurveAffine

variable {F : Type u} [Field F] [DecidableEq F] (W : WeierstrassCurve.Affine F) [W.IsElliptic]

/-- **A nonempty `[n]`-fiber on `W.Point` has as many points as `W.Point[n]`.**  The
Mathlib-side replacement of `TauCeti.Isogeny.card_zsmul_fiber_eq_card_ker`. -/
theorem natCard_zsmul_fiber_eq_card_torsionBy (n : ℤ) {T P₀ : W.Point} (hP₀ : n • P₀ = T) :
    Nat.card {P : W.Point // n • P = T} = Nat.card (AddSubgroup.torsionBy W.Point n) :=
  natCard_zsmulFiber_eq_natCard_torsionBy (A := W.Point) n hP₀

/-- **The exact first field of the D5 cardinality port**: the `n`-torsion of the `F`-points of
`W` has `n.natAbs ^ 2` elements.

In TauCeti this is the conclusion of
`TauCeti.Isogeny.card_ker_mulByIntIsogeny_of_torsion_rational` (and of
`WeierstrassCurve.Affine.natCard_torsionBy_of_torsion_rational` read on
`AddSubgroup.torsionBy`).  Its source proof goes through the separable degree of the
multiplication-by-`n` isogeny and the rationality of the geometric `n`-torsion; neither that
isogeny nor a separable-degree theory of curve function fields is available here, so the
statement is kept as the named input, not replaced by a hypothesis of a different shape. -/
def TorsionCardinalityAt (n : ℤ) : Prop :=
  Nat.card (AddSubgroup.torsionBy W.Point n) = n.natAbs ^ 2

/-- **`[n]` is `n ^ 2`-to-one over a nonempty fiber**, the port of
`TauCeti.Isogeny.card_zsmul_fiber`, from the exact first field. -/
theorem card_zsmul_fiber (n : ℤ) (h : TorsionCardinalityAt W n) {T P₀ : W.Point}
    (hP₀ : n • P₀ = T) :
    Nat.card {P : W.Point // n • P = T} = n.natAbs ^ 2 := by
  rw [natCard_zsmul_fiber_eq_card_torsionBy W n hP₀]
  exact h

/-- **The first field is exactly the fiber-count family**: the cardinality of `W.Point[n]` is
`n.natAbs ^ 2` if and only if every nonempty `[n]`-fiber has `n.natAbs ^ 2` points.  Hence the
reduction above loses no content, and the first field is the minimal exact input for the
ported `card_zsmul_fiber`. -/
theorem torsionCardinalityAt_iff_card_fiber (n : ℤ) :
    TorsionCardinalityAt W n ↔
      ∀ T P₀ : W.Point, n • P₀ = T → Nat.card {P : W.Point // n • P = T} = n.natAbs ^ 2 := by
  constructor
  · intro h T P₀ hP₀
    exact card_zsmul_fiber W n h hP₀
  · intro h
    have h0 : Nat.card {P : W.Point // n • P = 0} = n.natAbs ^ 2 := h 0 0 (by simp)
    have h1 : Nat.card (AddSubgroup.torsionBy W.Point n) = Nat.card {P : W.Point // n • P = 0} :=
      rfl
    unfold TorsionCardinalityAt
    rw [h1, h0]

/-- **Finiteness of the `n`-torsion from its cardinality**, the port of
`WeierstrassCurve.Affine.finite_torsionBy` at the exact first field: a nonzero `Nat.card`
cannot be infinite, and `Nat.card` is `0` on infinite types. -/
theorem finite_torsionBy_of_torsionCardinalityAt (n : ℤ) (hn : n ≠ 0)
    (h : TorsionCardinalityAt W n) : Finite (AddSubgroup.torsionBy W.Point n) := by
  have hcard : Nat.card (AddSubgroup.torsionBy W.Point n) = n.natAbs ^ 2 := h
  rw [← not_infinite_iff_finite]
  intro hinf
  haveI := hinf
  rw [Nat.card_eq_zero_of_infinite] at hcard
  have hne : n.natAbs ^ 2 ≠ 0 := by
    have hn' : n.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hn
    positivity
  exact hne hcard.symm

/-- The prime form of the first field, in the shape D5 consumes (`l` prime, `l >= 5`). -/
theorem natCard_torsionBy_prime (l : ℕ) (h : TorsionCardinalityAt W (l : ℤ)) :
    Nat.card (AddSubgroup.torsionBy W.Point (l : ℤ)) = l ^ 2 := by
  have hcard : Nat.card (AddSubgroup.torsionBy W.Point (l : ℤ)) = (l : ℤ).natAbs ^ 2 := h
  rwa [Int.natAbs_natCast] at hcard

/-- The prime form of `card_zsmul_fiber`: the port of
`TauCeti.Isogeny.card_ker_mulByPrimeIsogeny_of_torsion_rational` read on fibers, from the
exact first field at `l`. -/
theorem card_zsmul_fiber_prime (l : ℕ) (h : TorsionCardinalityAt W (l : ℤ))
    {T P₀ : W.Point} (hP₀ : (l : ℤ) • P₀ = T) :
    Nat.card {P : W.Point // (l : ℤ) • P = T} = l ^ 2 := by
  rw [card_zsmul_fiber W (l : ℤ) h hP₀]
  rw [Int.natAbs_natCast]

/-- The first field at `n = 1`, so the first field is not vacuous. -/
theorem torsionCardinalityAt_one : TorsionCardinalityAt W (1 : ℤ) := by
  show Nat.card (AddSubgroup.torsionBy W.Point (1 : ℤ)) = (1 : ℤ).natAbs ^ 2
  rw [natCard_torsionBy_one]
  norm_num

/-- The first field at `n = -1`. -/
theorem torsionCardinalityAt_neg_one : TorsionCardinalityAt W (-1 : ℤ) := by
  show Nat.card (AddSubgroup.torsionBy W.Point (-1 : ℤ)) = (-1 : ℤ).natAbs ^ 2
  rw [natCard_torsionBy_neg_one]
  norm_num

end WeierstrassCurveAffine

end LeanFormal.IUT.XiFPaper.S1395TorsionCardinalityPortActual
