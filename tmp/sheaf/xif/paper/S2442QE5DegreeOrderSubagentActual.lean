/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/

import tmp.sheaf.xif.paper.S2298QE5OrderActual
import tmp.sheaf.xif.paper.S2301DegreeEqOrderActual
import tmp.sheaf.xif.paper.S2304GaloisGroupIsoActual
import tmp.sheaf.xif.paper.S2310GaloisIsoActual
import tmp.sheaf.xif.paper.S2315GaloisImageIsoActual
import tmp.sheaf.xif.paper.S2319KernelQuotIsoActual
import tmp.sheaf.xif.paper.S2325DomainComparisonActual
import tmp.sheaf.xif.paper.S2328RestrictionMapActual
import tmp.sheaf.xif.paper.S2253LinearDisjointActual
import tmp.sheaf.xif.paper.S2445D5LargeImageChainActual
import tmp.sheaf.xif.paper.S1982D5FiveActual
import tmp.sheaf.xif.paper.S2055DicksonClassActual

/-!
# S2442: the degree = image-order identification, actual attack

## The target under attack

The tree identifies the degree of the absolute 5-division field with the order
of the mod-5 matrix image:

* `S2298QE5DegreeEqualsImageOrderRequired H : Module.finrank Q s2289QE5 = Nat.card H`
  (S2298), consumed by `S2445DegreeEqImageOrder` (S2445);
* its structural form, the domain comparison
  `S2319GalIsoMatrixQuotRequired b : Nonempty (S2304Gal ≃* (Gal(F'/F') / matrixKernel b))`
  (S2319), packaged as `S2325RestrictionData` / `S2328ExactFirstMissing`
  (S2325, S2328);
* every bridge in S2301/S2304/S2310/S2315 assumes the same
  `finrank = Nat.card (matrix image)` shape.

This file attacks that identification with the actual objects of S2289/S2294
(the degree), S2301/S2304/S2310 (the Galois group `S2304Gal = Polynomial.Gal psi5`),
S2315 (the first isomorphism theorem for the matrix image) and S2319/S2325/S2328
(the domain comparison).  The outcome is not a proof but a *refutation*: the
identification misses the central involution `-I` of `GL_2(F_5)`, i.e. an exact
factor of two.

## The mathematics

`S2057Psi5Q = S1667Curve.prePsi 5` is the odd 5-division polynomial.  By S2056 it
has degree 12, is separable, and its twelve roots are the twelve pairs
`{P, -P}` of nonzero 5-torsion points.  Consequently

  `s2289QE5 = SplittingField S2057Psi5Q = Q(x(P) : P in E[5], P ≠ 0)`

is the field of the *x-coordinates* of the 5-torsion points, and NOT the full
5-division field `Q(E[5]) = Q(x(P), y(P))`.

For `sigma` in the mod-5 image `G <= GL_2(F_5)` one has `sigma(x(P)) = x(sigma P)`.
Since the twelve pairs are distinct, `sigma` fixes all twelve x-coordinates iff
`sigma P = ±P` for every nonzero `P`.  A sign function `eps` with
`sigma P = eps(P) P` is constant on nonzero `P` (if `eps(P) = -eps(Q)` then
`sigma(P+Q) = eps(P)(P-Q)` forces `P = ±Q`, hence `P = -Q`, i.e.
`eps(P) = eps(Q)`), so this is equivalent to `sigma = ±I`.  Therefore

  `Gal(Q(x(P))/Q) = G / (G cap {±I})`,  `[Q(x(P)) : Q] = |G| / |G cap {±I}|`.

Under full image `G = GL_2(F_5)` -- exactly what the Dickson hypotheses of
S2055/S2298/S2445 produce, and hence `-I in G` -- this gives

  `[Q(x(P)) : Q] = 480 / 2 = 240`,

not 480.  So `S2298QE5DegreeEqualsImageOrderRequired H` (with `|H| = 480`) is
false, and the domain comparison `S2319GalIsoMatrixQuotRequired` / the
restriction data of `S2325RestrictionData` are false as well: their kernel
`S2315MatrixKernel b` is too small by `{±I}`, because the correct quotient is by
the preimage of `{±I}`, equivalently by the kernel of the action on the twelve
pairs.

## What is kernel-checked here

No sorry, no axiom, no True/PUnit/Nonempty-of-the-target gate, no
native_decide, no renamed or weakened hypothesis.  The single new hypothesis is
the honest, named, *true* statement

  `S2442Psi5ProjectiveBridge : Nonempty (S2304Gal ≃* (GL_2(F_5) / {±I}))`

which is precisely the missing `psi5`-root to pair Galois equivariance (the same
missing bridge S2056 names as the "Galois-equivariant x-coordinate bijection",
and the S1987 report names as the division-field/Galois correspondence).  It is
not derivable in the tree, and it is *not* a way of assuming the conclusion: it
is the statement that pins the true degree to 240.

Contents, all unconditional except where the bridge is an explicit hypothesis:

* the actual central involution `-I` of `GL_2(F_5)`: `S2442NegOne`,
  `S2442NegOne_val`, `S2442NegOne_sq`, `S2442NegOne_ne_one`,
  `S2442NegOne_orderOf`;
* the projective index computation: `S2442Central_card` (`|{±I}| = 2`),
  `S2442Central_index` (`[GL_2(F_5) : {±I}] = 240`), `S2442Quotient_card`
  (`|GL_2(F_5)/{±I}| = 240`), from `natCard_GL2 : |GL_2(F_5)| = 480`;
* `S2442Gal_card_eq_240`, `S2442Degree_eq_240` (`[Q(x(P)) : Q] = 240` under the
  bridge), `S2442Degree_ne_480`;
* the refutations: `S2442NotDegreeEqImageOrder`,
  `S2442NotS2445DegreeEqImageOrder`, `S2442NotGalIsoMatrixQuot`,
  `S2442NotRestrictionDataRequired`, `S2442NotS2328ExactFirstMissing`;
* the unconditional implication that documents what the domain comparison would
  give: `S2442DegreeEqImageOrder_of_restrictionData`;
* the corrected targets: `S2442CorrectedDegreeEqProjectiveOrder` (degree = order
  of the projective image), `S2442PairAction` /
  `S2442CorrectedDomainComparison` (Gal(psi5/Q) is the image of `Gal(F'/F')` in the
  permutations of the twelve pairs), `S2442Degree_eq_half_imageOrder`.

## Consequence for the tree

`Module.finrank Q s2289QE5 = 480` is not a theorem and cannot become one: the
true value is 240.  A consumer that genuinely needs 480 must either
(a) replace `s2289QE5` by the *full* 5-division field `Q(E[5]) = Q(x(P), y(P))`,
whose degree is `|G| = 480` and which is not constructed anywhere in the tree,
or
(b) use the corrected value `240 = |GL_2(F_5)/{±I}|`, i.e. the order of the
action on the twelve pairs / of the image in `PGL_2(F_5)`.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2442QE5DegreeOrderSubagentActual

open Matrix
open LeanFormal.IUT.XiFPaper.S2009DicksonActual
open LeanFormal.IUT.XiFPaper.S2289QE5DegreeActual
open LeanFormal.IUT.XiFPaper.S2298QE5OrderActual
open LeanFormal.IUT.XiFPaper.S2304GaloisGroupIsoActual
open LeanFormal.IUT.XiFPaper.S2310GaloisIsoActual
open LeanFormal.IUT.XiFPaper.S2315GaloisImageIsoActual
open LeanFormal.IUT.XiFPaper.S2319KernelQuotIsoActual
open LeanFormal.IUT.XiFPaper.S2325DomainComparisonActual
open LeanFormal.IUT.XiFPaper.S2328RestrictionMapActual
open LeanFormal.IUT.XiFPaper.S2445D5LargeImageChainActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual

/-! ## 1. The central involution -I of GL_2(F_5) -/

/-- The central involution -I of GL_2(F_5), realized as the scalar unit -1. -/
def S2442NegOne : GL2 :=
  Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (-1 : ZMod 5) (by norm_num))

/-- The underlying matrix of S2442NegOne is -1. -/
theorem S2442NegOne_val :
    (S2442NegOne : Matrix (Fin 2) (Fin 2) (ZMod 5)) = -1 := by
  rw [S2442NegOne, Matrix.GeneralLinearGroup.coe_scalar]
  ext i j
  by_cases h : i = j
  . subst h
    simp [Matrix.scalar_apply, Units.val_mk0]
  . simp [Matrix.scalar_apply, h]

/-- S2442NegOne is an involution. -/
theorem S2442NegOne_sq : S2442NegOne ^ 2 = 1 := by
  have hu : (Units.mk0 (-1 : ZMod 5) (by norm_num)) ^ 2 = 1 := by
    ext
    simp [Units.val_mk0]
  rw [S2442NegOne, ← MonoidHom.map_pow, hu, MonoidHom.map_one]

/-- -I is not the identity of GL_2(F_5). -/
theorem S2442NegOne_ne_one : S2442NegOne ≠ 1 := by
  intro h
  have hv : (S2442NegOne : Matrix (Fin 2) (Fin 2) (ZMod 5)) = 1 := by
    simpa using congrArg
      (fun x : GL2 => (x : Matrix (Fin 2) (Fin 2) (ZMod 5))) h
  rw [S2442NegOne_val] at hv
  have h00 : ((-1 : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 0) =
      ((1 : Matrix (Fin 2) (Fin 2) (ZMod 5)) 0 0) :=
    congrFun (congrFun hv 0) 0
  rw [Matrix.neg_apply, Matrix.one_apply, if_pos (rfl : (0 : Fin 2) = 0)] at h00
  have hne : ((-1 : ZMod 5)) ≠ 1 := by decide
  exact hne h00

/-- -I has order two. -/
theorem S2442NegOne_orderOf : orderOf S2442NegOne = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime S2442NegOne_sq S2442NegOne_ne_one

/-- The central subgroup {±I} has two elements. -/
theorem S2442Central_card :
    Nat.card (Subgroup.zpowers S2442NegOne) = 2 := by
  rw [Nat.card_zpowers, S2442NegOne_orderOf]


/-- The subgroup {±I} is normal (it is generated by a central scalar). -/
instance S2442Central_normal : (Subgroup.zpowers S2442NegOne).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_zpowers_iff] at hn ⊢
  obtain ⟨k, hk⟩ := hn
  subst hk
  refine ⟨k, ?_⟩
  have hcomm : S2442NegOne * g = g * S2442NegOne := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [S2442NegOne_val, Matrix.mul_apply, Finset.sum_neg_distrib]
  have hc : Commute S2442NegOne g := hcomm
  have hc' : Commute (S2442NegOne ^ k) g := (hc.symm.zpow_right k).symm
  have hconj : g * S2442NegOne ^ k * g⁻¹ = S2442NegOne ^ k := by
    rw [← hc'.eq]
    group
  exact hconj.symm

/-- The index of {±I} in GL_2(F_5) is 240. -/
theorem S2442Central_index :
    (Subgroup.zpowers S2442NegOne).index = 240 := by
  have h := Subgroup.card_mul_index (Subgroup.zpowers S2442NegOne)
  rw [S2442Central_card, natCard_GL2] at h
  omega

/-- |GL_2(F_5)/{±I}| = 240: the order of the action on the twelve pairs {P,-P},
and the true degree of the splitting field of psi5. -/
theorem S2442Quotient_card :
    Nat.card (GL2 ⧸ Subgroup.zpowers S2442NegOne) = 240 := by
  rw [← Subgroup.index_eq_card, S2442Central_index]

/-! ## 2. The missing bridge and the true degree -/

/-- The exact missing identification, in its sharpest form: the Galois group of
psi5 over Q is the projective image GL_2(F_5)/{±I} of the mod-5 representation.
This is precisely the psi5-root to pair {P,-P} Galois equivariance.  It is a true
statement about the actual curve and is *not* derivable in the tree; it is
recorded as an explicit hypothesis, never assumed silently. -/
structure S2442Psi5ProjectiveBridge where
  iso : S2304Gal ≃* (GL2 ⧸ Subgroup.zpowers S2442NegOne)

/-- The bridge, as a Prop. -/
def S2442Psi5ProjectiveBridgeRequired : Prop :=
  Nonempty S2442Psi5ProjectiveBridge

/-- Under the bridge, the Galois group of psi5 has order 240. -/
theorem S2442Gal_card_eq_240 (D : S2442Psi5ProjectiveBridge) :
    Nat.card S2304Gal = 240 := by
  exact (Nat.card_congr D.iso.toEquiv).trans S2442Quotient_card

/-- Under the bridge, the actual degree of the splitting field of psi5 is 240,
not 480. -/
theorem S2442Degree_eq_240 (D : S2442Psi5ProjectiveBridge) :
    Module.finrank ℚ s2289QE5 = 240 := by
  rw [← S2304Gal_card_eq_finrank, S2442Gal_card_eq_240 D]

/-- The headline: the degree of s2289QE5 is not 480. -/
theorem S2442Degree_ne_480 (D : S2442Psi5ProjectiveBridge) :
    Module.finrank ℚ s2289QE5 ≠ 480 := by
  rw [S2442Degree_eq_240 D]
  norm_num

/-! ## 3. Refutation of S2298QE5DegreeEqualsImageOrderRequired -/

/-- The degree = image-order identification is false as soon as the image order
is 480 = |GL_2(F_5)|: the degree is 240. -/
theorem S2442NotDegreeEqImageOrder (H : Subgroup GL2)
    (D : S2442Psi5ProjectiveBridge) (hH : Nat.card H = 480) :
    ¬ (S2298QE5DegreeEqualsImageOrderRequired H) := by
  intro hdeg
  unfold S2298QE5DegreeEqualsImageOrderRequired at hdeg
  rw [S2442Degree_eq_240 D, hH] at hdeg
  exact absurd hdeg (by norm_num)

/-- The actual image order is 480 under the S2055/S2298 Dickson hypotheses. -/
theorem S2442ImageCard_eq_480
    (hdet : S2445RangeDetSurjective) (hpair : S2445RangePairTransitive)
    (hcycle : S2445RangeCycleType) :
    Nat.card
      (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis).range = 480 :=
  S2298ImageCard_eq_480_of_hypotheses _ hdet hpair hcycle

/-- The S2445 target is false: under the very hypotheses that S2445 uses to
compute the image order 480, the degree of s2289QE5 is 240. -/
theorem S2442NotS2445DegreeEqImageOrder
    (D : S2442Psi5ProjectiveBridge)
    (hdet : S2445RangeDetSurjective) (hpair : S2445RangePairTransitive)
    (hcycle : S2445RangeCycleType) :
    Not S2445DegreeEqImageOrder :=
  S2442NotDegreeEqImageOrder _ D (S2442ImageCard_eq_480 hdet hpair hcycle)

/-! ## 4. What the domain comparison would give, and why it cannot hold -/

/-- Unconditional: the domain comparison (S2325 restriction data) would give the
identification.  This is the exact route the tree proposed for the actual basis
S1982Basis; the next theorems show its premise is refutable. -/
theorem S2442DegreeEqImageOrder_of_restrictionData
    (R : S2325RestrictionData S1982Basis) :
    S2445DegreeEqImageOrder :=
  S2310Degree_eq_imageOrder_of_iso _
    (S2325S2310Iso_of_restriction S1982Basis R).some

/-- The domain comparison S2319GalIsoMatrixQuotRequired is false: by the S2315
first isomorphism theorem the matrix quotient has order |range| = 480, while
S2304Gal has order 240. -/
theorem S2442NotGalIsoMatrixQuot (b : S1725TorsionBasis S1987Five)
    (D : S2442Psi5ProjectiveBridge)
    (hH : Nat.card
      (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range = 480) :
    ¬ (S2319GalIsoMatrixQuotRequired b) := by
  rintro ⟨e⟩
  have h1 : Nat.card S2304Gal = 240 := S2442Gal_card_eq_240 D
  have h2 : Nat.card (S2315GalF' ⧸ S2315MatrixKernel b) =
      Nat.card (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range :=
    Nat.card_congr (S2315MatrixQuotEquiv b).toEquiv
  have h3 : Nat.card S2304Gal =
      Nat.card (S2315GalF' ⧸ S2315MatrixKernel b) :=
    Nat.card_congr e.toEquiv
  rw [h1, h2, hH] at h3
  exact absurd h3 (by norm_num)

/-- The restriction data S2325RestrictionDataRequired is false: its kernel
condition ker = matrixKernel is too small by the central subgroup {±I}. -/
theorem S2442NotRestrictionDataRequired (b : S1725TorsionBasis S1987Five)
    (D : S2442Psi5ProjectiveBridge)
    (hH : Nat.card
      (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range = 480) :
    ¬ (S2325RestrictionDataRequired b) := by
  rintro ⟨R⟩
  exact S2442NotGalIsoMatrixQuot b D hH
    (S2325GalIsoMatrixQuot_of_restriction b R)

/-- S2328ExactFirstMissing is false at any basis whose matrix image has order
480 (in particular the actual S1982Basis under the S2445 hypotheses). -/
theorem S2442NotS2328ExactFirstMissing (b : S1725TorsionBasis S1987Five)
    (D : S2442Psi5ProjectiveBridge)
    (hH : Nat.card
      (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range = 480) :
    ¬ (S2328ExactFirstMissing b) := by
  rintro ⟨h, _⟩
  exact S2442NotRestrictionDataRequired b D hH h

/-! ## 5. The corrected targets -/

/-- The corrected degree identification: the degree of the splitting field of
psi5 is the order of the projective image GL_2(F_5)/{±I} (equivalently the
order of the action on the twelve pairs), not of the linear image. -/
def S2442CorrectedDegreeEqProjectiveOrder : Prop :=
  Module.finrank ℚ s2289QE5 =
    Nat.card (GL2 ⧸ Subgroup.zpowers S2442NegOne)

/-- Under the bridge, the corrected identification holds. -/
theorem S2442CorrectedDegree_of_bridge (D : S2442Psi5ProjectiveBridge) :
    S2442CorrectedDegreeEqProjectiveOrder := by
  unfold S2442CorrectedDegreeEqProjectiveOrder
  rw [S2442Degree_eq_240 D, S2442Quotient_card]

/-- The actual action of Gal(F'/F') on the twelve pairs {P,-P} of the mod-5
image at a rank-two basis b. -/
noncomputable def S2442PairAction (b : S1725TorsionBasis S1987Five) :
    S2315GalF' →* Equiv.Perm S2009Pairs :=
  pairPermHom.comp (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b)

/-- The corrected domain comparison: Gal(psi5/Q) is (the range of) the action of
Gal(F'/F') on the twelve pairs.  This is the quotient by the preimage of {±I},
i.e. by the kernel of the pair action, and it is the honest replacement for
S2319GalIsoMatrixQuotRequired. -/
def S2442CorrectedDomainComparison (b : S1725TorsionBasis S1987Five) : Prop :=
  Nonempty (S2304Gal ≃* (S2442PairAction b).range)

/-- The corrected domain comparison computes the actual degree. -/
theorem S2442CorrectedDegree_of_domainComparison
    (b : S1725TorsionBasis S1987Five) (D : S2442CorrectedDomainComparison b) :
    Module.finrank ℚ s2289QE5 = Nat.card (S2442PairAction b).range := by
  rw [← S2304Gal_card_eq_finrank]
  exact Nat.card_congr D.some.toEquiv

/-- The corrected degree formula in image-order form: the degree is half the
matrix image order. -/
theorem S2442Degree_eq_half_imageOrder (H : Subgroup GL2)
    (D : S2442Psi5ProjectiveBridge) (hH : Nat.card H = 480) :
    Module.finrank ℚ s2289QE5 = Nat.card H / 2 := by
  rw [S2442Degree_eq_240 D, hH]

/-! ## 6. Axiom footprint -/

#print axioms S2442NegOne_val
#print axioms S2442NegOne_sq
#print axioms S2442NegOne_ne_one
#print axioms S2442NegOne_orderOf
#print axioms S2442Central_card
#print axioms S2442Central_index
#print axioms S2442Quotient_card
#print axioms S2442Gal_card_eq_240
#print axioms S2442Degree_eq_240
#print axioms S2442Degree_ne_480
#print axioms S2442NotDegreeEqImageOrder
#print axioms S2442ImageCard_eq_480
#print axioms S2442NotS2445DegreeEqImageOrder
#print axioms S2442DegreeEqImageOrder_of_restrictionData
#print axioms S2442NotGalIsoMatrixQuot
#print axioms S2442NotRestrictionDataRequired
#print axioms S2442NotS2328ExactFirstMissing
#print axioms S2442CorrectedDegree_of_bridge
#print axioms S2442CorrectedDegree_of_domainComparison
#print axioms S2442Degree_eq_half_imageOrder

end LeanFormal.IUT.XiFPaper.S2442QE5DegreeOrderSubagentActual

end
