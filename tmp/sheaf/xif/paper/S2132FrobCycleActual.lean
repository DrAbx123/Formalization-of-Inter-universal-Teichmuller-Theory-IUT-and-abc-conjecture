/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/
import tmp.sheaf.xif.paper.S2057DedekindFrobBridgeActual
import tmp.sheaf.xif.paper.S2055DicksonClassActual
import tmp.sheaf.xif.paper.S2056Psi5RootsPairsActual
import tmp.sheaf.xif.paper.S2041D5LargeImageFirstMilestoneActual
import tmp.sheaf.xif.paper.S1942PrePsiFiveActual
import tmp.sheaf.xif.paper.S2132D5FactorizationActual
import tmp.sheaf.xif.paper.S2126Mod29IntegrationActual

/-!
# S2132: the Frobenius cycle-type bridge on the twelve pairs

The S1987 report step (2) for the l = 5 large-image input says that the
Frobenius at 29 acts on the twelve pairs {+-P} of nonzero 5-torsion points with
cycle type (10, 2), because the odd 5-division polynomial psi_5 factors modulo
29 as an irreducible quadratic times an irreducible degree-ten factor.

This file separates what is actually proved from what is missing.

## Proved here (kernel checked)

* S2132PairCycle_exists: there is a permutation of the twelve-element type
  S2056Pair of negation-closed two-element sets of nonzero 5-torsion points
  whose cycle type is (10, 2).  This is the transported S2009 finite-group
  permutation; it is not asserted to come from Frobenius.
* S2132DivisionRoots_card and the Galois action S2132DivisionRootEquiv on the
  twelve roots of psi_5 in the actual splitting field S2057FiveDivisionField
  over F' = S1720Field (S2057).
* S2132Bridge_of_factorization: the S2057 Frobenius cycle-type bridge
  structure is inhabited as soon as its mod-29 factorization field is, with no
  Frobenius input at all.  This shows the structure is too weak: its
  frobenius and permutation fields are unrelated, so it is not the honest
  bridge.  Consequence: S2041Psi5Remaining reduces to Nonempty
  S2057Mod29FactorizationData.
* S2132ImageTail_of_cycleType_and_transitive: a subgroup of GL_2(F_5)
  containing an element of cycle type (10, 2) and acting transitively on the
  twelve pairs contains the image of SL_2(F_5) (S2020 route).  Applied at an
  actual basis this gives S2132D5LargeImageFive_of_rangeHypotheses: the D5
  target follows from HasCycleType102 and PairTransitive for the actual mod-5
  image.  This is a conditional reduction, not a proof of D5; both hypotheses
  remain unproved.
* S2132NoIntegerModel and S2132Mod29FactorizationData_empty: the mod-29 datum
  S2057Mod29FactorizationData is UNINHABITABLE as defined.  The actual psi_5
  has constant coefficient 3814697265625 / 2^36
  (S2132Psi5Q_eval_zero), so no integer-coefficient polynomial maps to it;
  the integerModel field demands exactly such a polynomial.  Consequently
  S2041Psi5Remaining is FALSE as formalized (S2132S2041Psi5Remaining_false).
  Repairing the mod-29 datum is a target change, not a missing proof.

## Exact first missing

S2132FrobInducesPairCycleType says: there is an F'-automorphism of the actual
splitting field S2057FiveDivisionField whose induced permutation of the twelve
roots (equivalently, of the twelve pairs) has cycle type (10, 2).

This is the precise arithmetic bridge.  It is NOT proved here.  The missing
inputs are:

1. an actual Frobenius element at a prime above 29 in the splitting field
   (Mathlib's number-field library has Ideal.inertiaDeg and
   primesOverSpanEquivMonicFactorsMod, but no Frobenius element of a Galois
   extension, and no theorem relating its cycle type on roots to the residual
   factorization);
2. a repaired mod-29 factorization interface.  The monic product statement
   recorded in S2132D5FactorizationActual is false (S2132RecordedProduct_false):
   the true product carries the scalar 4 (S2132CorrectedProduct).  More
   seriously, the integerModel field of S2057Mod29FactorizationData is
   unsatisfiable: psi_5 is not integral (S2132NoIntegerModel), so the datum
   cannot be inhabited at all.  Any repair is a target change.

No sorry, admit, axiom, native_decide or opaque declaration is used.
The axiom footprint of every declaration is printed at the end.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

open Polynomial
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S2009DicksonActual
open LeanFormal.IUT.XiFPaper.S2055DicksonClassActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S2056Psi5RootsActual
open LeanFormal.IUT.XiFPaper.S2056Psi5RootsPairsActual
open LeanFormal.IUT.XiFPaper.S2041D5LargeImageFirstMilestoneActual
open LeanFormal.IUT.XiFPaper.S1942PrePsiFiveActual
open LeanFormal.IUT.XiFPaper.S1667AdmissibleCurveActual

namespace LeanFormal.IUT.XiFPaper.S2132FrobCycleActual

/-! ## 1. Cycle types of permutations of the twelve actual pairs -/

/-- Relabelling preserves disjointness of permutations. -/
theorem S2132disjoint_permCongr {α β : Type*} {e : α ≃ β} {f g : Equiv.Perm α}
    (h : Equiv.Perm.Disjoint f g) :
    Equiv.Perm.Disjoint (e.permCongr f) (e.permCongr g) := by
  rw [Equiv.Perm.disjoint_iff_eq_or_eq] at h ⊢
  intro y
  rcases h (e.symm y) with hf | hg
  · left; simp [Equiv.permCongr_apply, hf]
  · right; simp [Equiv.permCongr_apply, hg]

/-- The cycle type of a permutation is invariant under relabelling.  Proved by
the cycle decomposition of Equiv.Perm.cycle_induction_on. -/
theorem S2132cycleType_permCongr {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (e : α ≃ β) (σ : Equiv.Perm α) :
    (e.permCongr σ).cycleType = σ.cycleType := by
  induction σ using Equiv.Perm.cycle_induction_on with
  | base_one => simpa using map_one (Equiv.permCongrHom e)
  | base_cycles σ hσ =>
      rw [(isCycle_permCongr (e := e) hσ).cycleType, hσ.cycleType,
        card_support_permCongr e σ]
  | induction_disjoint σ τ hd hc hσ hτ =>
      rw [Equiv.permCongr_mul, hd.cycleType_mul,
        (S2132disjoint_permCongr (e := e) hd).cycleType_mul, hσ, hτ]

/-- The twelve actual pairs have cardinality twelve (S2056). -/
theorem S2132Pair_card_fintype : Fintype.card S2056Pair = 12 := by
  rw [← Nat.card_eq_fintype_card, S2056Pair_card]

/-- A bijection between the twelve actual pairs and the S2009 finite model
F_5^2 / +- . -/
noncomputable def S2132PairEquivS2009 : S2009Pairs ≃ S2056Pair :=
  Fintype.equivOfCardEq (by rw [card_pairRep, S2132Pair_card_fintype])

/-- An explicit permutation of the twelve actual pairs with cycle type
(10, 2), obtained by transporting the S2009 element C (the class of the matrix
!![0,1;1,1]).  This says only that the cycle type is realised by some
permutation of the twelve pairs. -/
noncomputable def S2132PairCycle : Equiv.Perm S2056Pair :=
  S2132PairEquivS2009.permCongr (LeanFormal.IUT.XiFPaper.S2009DicksonActual.C)

/-- The transported permutation has cycle type (10, 2). -/
theorem S2132PairCycle_cycleType :
    S2132PairCycle.cycleType = ({2, 10} : Multiset Nat) := by
  rw [S2132PairCycle, S2132cycleType_permCongr,
    LeanFormal.IUT.XiFPaper.S2009DicksonActual.cycleType_C]
  decide

/-- The cycle type (10, 2) is realised on the actual twelve pairs. -/
theorem S2132PairCycle_exists :
    ∃ ρ : Equiv.Perm S2056Pair, ρ.cycleType = ({2, 10} : Multiset Nat) :=
  ⟨S2132PairCycle, S2132PairCycle_cycleType⟩

/-- The finite-group content of the (10, 2) input: the whole group GL_2(F_5)
meets the cycle type, already in S2009. -/
theorem S2132HasCycleType102_top : HasCycleType102 (⊤ : Subgroup GL2) :=
  hasCycleType102_top

/-! ## 2. The actual Galois action on the twelve roots over F' -/

/-- The actual splitting field of psi_5 over F' = S1720Field (S2057). -/
abbrev S2132L : Type := S2057FiveDivisionField

instance S2132LDecEq : DecidableEq S2132L := Classical.decEq _

/-- The twelve roots of psi_5 in the actual splitting field. -/
abbrev S2132DivisionRoots : Type := S2057Psi5F.rootSet S2132L

instance S2132DivisionRootsDecEq : DecidableEq S2132DivisionRoots := Classical.decEq _

/-- psi_5 splits in its splitting field. -/
theorem S2132Psi5L_splits :
    (S2057Psi5F.map (algebraMap S1720Field S2132L)).Splits :=
  Polynomial.SplittingField.splits (f := S2057Psi5F)

/-- There are exactly twelve roots in the actual splitting field. -/
theorem S2132DivisionRoots_card : Fintype.card S2132DivisionRoots = 12 := by
  have h := Polynomial.card_rootSet_eq_natDegree (p := S2057Psi5F) (K := S2132L)
    S2057Psi5F_separable S2132Psi5L_splits
  have hdeg : S2057Psi5F.natDegree = 12 := by
    rw [S2057Psi5F, Polynomial.natDegree_map]
    simpa [S2057Psi5Q, S2056Psi5] using S2056Psi5_natDegree
  rw [h, hdeg]

/-- The action of an F'-automorphism of the splitting field on the twelve
roots. -/
noncomputable def S2132DivisionRootMap (σ : S2132L ≃ₐ[S1720Field] S2132L)
    (x : S2132DivisionRoots) : S2132DivisionRoots :=
  ⟨σ x.1, Polynomial.rootSet_mapsTo (p := S2057Psi5F) σ.toAlgHom x.2⟩

/-- The action of an F'-automorphism of the splitting field as a permutation
of the twelve roots. -/
noncomputable def S2132DivisionRootEquiv (σ : S2132L ≃ₐ[S1720Field] S2132L) :
    S2132DivisionRoots ≃ S2132DivisionRoots where
  toFun := S2132DivisionRootMap σ
  invFun := S2132DivisionRootMap σ.symm
  left_inv x := by apply Subtype.ext; exact σ.symm_apply_apply x.1
  right_inv x := by apply Subtype.ext; exact σ.apply_symm_apply x.1

/-- A fixed bijection between the twelve roots over the splitting field and
the twelve actual pairs {+-P} of S2056.  Both types are twelve-element sets,
so only cardinality is used; the cycle type below is independent of this
choice. -/
noncomputable def S2132DivisionRootPairEquiv :
    S2132DivisionRoots ≃ S2056Pair :=
  Fintype.equivOfCardEq
    (S2132DivisionRoots_card.trans S2132Pair_card_fintype.symm)

/-- **The honest Frobenius cycle-type statement.**  There is an
F'-automorphism of the actual splitting field of psi_5 whose induced
permutation of the twelve roots has cycle type (10, 2).  Equivalently (the
cycle type is invariant under the relabelling S2132DivisionRootPairEquiv), its
induced permutation of the twelve actual pairs has cycle type (10, 2).

This is the precise replacement for the too-weak
S2057FrobMod29CycleTypeBridge: it relates the Galois automorphism to the
permutation.  It is NOT proved in this file. -/
def S2132FrobInducesPairCycleType : Prop :=
  ∃ σ : S2132L ≃ₐ[S1720Field] S2132L,
    Equiv.Perm.cycleType
      (S2132DivisionRootPairEquiv.permCongr (S2132DivisionRootEquiv σ)) =
        ({2, 10} : Multiset Nat)

/-- The root form of the honest statement. -/
def S2132FrobInducesRootCycleType : Prop :=
  ∃ σ : S2132L ≃ₐ[S1720Field] S2132L,
    Equiv.Perm.cycleType (S2132DivisionRootEquiv σ) = ({2, 10} : Multiset Nat)

/-- The root form and the pair form of the honest statement are equivalent. -/
theorem S2132FrobInduces_iff :
    S2132FrobInducesRootCycleType ↔ S2132FrobInducesPairCycleType := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨σ, by rw [S2132cycleType_permCongr, hσ]⟩
  · rintro ⟨σ, hσ⟩
    refine ⟨σ, ?_⟩
    have := hσ
    rw [S2132cycleType_permCongr] at this
    exact this

/-! ## 3. The S2057 package and the S2041 remaining input -/

/-- The S2057 Frobenius cycle-type bridge is constructed from any mod-29
factorization datum and the explicit family permutation of Section 1.  No
Frobenius element is used: in S2057FrobMod29CycleTypeBridge the frobenius and
permutation fields are independent, so this package is only bookkeeping, not
the arithmetic bridge. -/
noncomputable def S2132Bridge_of_factorization
    (fact : S2057Mod29FactorizationData) :
    S2057FrobMod29CycleTypeBridge where
  factorization := fact
  frobenius := AlgEquiv.refl
  permutation := S2132PairCycle
  cycleType_eq := S2132PairCycle_cycleType

/-- The honest statement, plus any mod-29 factorization datum, produces the
S2057 package.  (Again the frobenius field is refl; the honest content is the
permutation field.) -/
noncomputable def S2132Bridge_of_factorization_and_honest
    (fact : S2057Mod29FactorizationData) (h : S2132FrobInducesPairCycleType) :
    S2057FrobMod29CycleTypeBridge where
  factorization := fact
  frobenius := AlgEquiv.refl
  permutation := S2132DivisionRootPairEquiv.permCongr
    (S2132DivisionRootEquiv h.choose)
  cycleType_eq := h.choose_spec

/-- S2041Psi5Remaining is reduced to its factorization half: the cycle-type
bridge half is automatic from the explicit family permutation. -/
theorem S2132Psi5Remaining_of_factorization
    (h : Nonempty S2057Mod29FactorizationData) :
    S2041Psi5Remaining :=
  ⟨h, ⟨S2132Bridge_of_factorization h.some⟩⟩

/-! ## 4. The D5 reduction: cycle type plus transitivity gives the target -/

/-- A subgroup of GL_2(F_5) containing an element of cycle type (10, 2) and
acting transitively on the twelve pairs contains the image of SL_2(F_5).  This
is the S2020 route: 10 divides |H| gives 5 divides |H| (S2009
ten_dvd_natCard_of_mem_cycleType102), and sl_le_of_five_dvd produces the two
standard transvections, whose closure is the whole SL_2 image. -/
theorem S2132ImageTail_of_cycleType_and_transitive (H : Subgroup GL2)
    (h102 : HasCycleType102 H) (htrans : PairTransitive H) :
    Subgroup.map Matrix.SpecialLinearGroup.toGL
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K5)) ≤ H := by
  have h5 : 5 ∣ Nat.card H := by
    obtain ⟨h, hh, hc⟩ := h102
    exact dvd_trans (by norm_num : 5 ∣ 10)
      (ten_dvd_natCard_of_mem_cycleType102 hh hc)
  have hle := sl_le_of_five_dvd H htrans h5
  rwa [closure_trv_eq_map, closure_sl_eq_top] at hle

/-- **Conditional D5 reduction.**  At any actual rank-two basis b of E'[5], an
element of cycle type (10, 2) in the actual mod-5 image together with
transitivity of that image on the twelve pairs implies the S1987 D5
large-image target.  This is NOT a proof of D5: both hypotheses are open. -/
theorem S2132D5LargeImageFive_of_rangeHypotheses
    (b : S1725TorsionBasis S1987Five)
    (h102 : HasCycleType102
      (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range)
    (htrans : PairTransitive
      (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range) :
    S1987D5LargeImageFive :=
  (S1987D5LargeImageFive_iff_tail b).mpr
    (S2132ImageTail_of_cycleType_and_transitive _ h102 htrans)

/-- The same reduction from the S2057 range-hypothesis data (the determinant
hypothesis is unused). -/
theorem S2132D5LargeImageFive_of_rangeData
    (b : S1725TorsionBasis S1987Five) (D : S2057RangeHypothesesData b) :
    S1987D5LargeImageFive :=
  S2132D5LargeImageFive_of_rangeHypotheses b D.cycle_type_102 D.pair_transitive

/-! ## 5. Exact first missing -/

/-- The exact first missing statement of the Frobenius cycle-type bridge, in
the honest (Galois-action) form.  Not inhabited in this file. -/
abbrev S2132FirstMissing : Prop := S2132FrobInducesPairCycleType

/-- The honest statement would give the S2057 package (and hence the S2041
remaining input, together with any factorization datum). -/
theorem S2132Remaining_of_honest_and_factorization
    (hfact : Nonempty S2057Mod29FactorizationData)
    (h : S2132FrobInducesPairCycleType) :
    S2041Psi5Remaining :=
  ⟨hfact, ⟨S2132Bridge_of_factorization_and_honest hfact.some h⟩⟩

/-! ## 6. The mod-29 factorization: the recorded monic product is false -/

/-- Integer lift of the quadratic factor with the scalar forced by the leading
coefficient: over Z/29 this is 4 * (x^2 + 6x + 12), i.e. the polynomial with
canonical coefficients (19, 24, 4). -/
noncomputable def S2132F2Z : ℤ[X] := 19 + 24 * X + 4 * X^2

/-- Integer lift of the degree-ten factor, with the canonical coefficients of
the S2126 polynomial f = 10 + 24x + 16x^2 + 14x^3 + 24x^4 + 8x^5 + 5x^6 +
7x^7 + 25x^9 + x^10. -/
noncomputable def S2132F10Z : ℤ[X] :=
  10 + 24 * X + 16 * X^2 + 14 * X^3 + 24 * X^4 + 8 * X^5 + 5 * X^6 + 7 * X^7 +
    25 * X^9 + X^10

/-- Exact cofactor of the corrected factorization. -/
noncomputable def S2132QZ : ℤ[X] :=
  131541285015 + (-24) * X + 3367456896520 * X^2 +
    (-4601293103474) * X^3 + (-1744137931064) * X^4 +
    5691628137904 * X^5 + 3325704827573 * X^6 +
    (-3101660689665) * X^7 + (-949142068972) * X^8 +
    (-352900060707) * X^9 + (-252505200167) * X^10 +
    45171207764 * X^11 + 11848185644 * X^12

/-- The exact integer identity behind the corrected mod-29 factorization. -/
theorem S2132IntegerIdentity :
    LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual.S2132Psi5Z =
      S2132F2Z * S2132F10Z + 29 * S2132QZ := by
  unfold LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual.S2132Psi5Z
    S2132F2Z S2132F10Z S2132QZ
  simp only [map_ofNat, map_neg]
  ring

/-- **Corrected mod-29 product identity.**  The reduction of the integer model
is the product of the quadratic lift (19 + 24x + 4x^2) and the degree-ten lift
(10 + 24x + ... + x^10).  This is the factorization with the scalar 4 that the
monic statement of S2132D5FactorizationActual omits. -/
theorem S2132CorrectedProduct :
    S2132F2Z.map (Int.castRingHom (ZMod 29)) *
        S2132F10Z.map (Int.castRingHom (ZMod 29)) =
      LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual.S2132Psi5Z.map
        (Int.castRingHom (ZMod 29)) := by
  have h := congrArg
    (Polynomial.map (Int.castRingHom (ZMod 29))) S2132IntegerIdentity
  simp only [Polynomial.map_add, Polynomial.map_mul] at h
  rw [h]
  have h29 : ((29 : ℤ[X]).map (Int.castRingHom (ZMod 29))) = 0 := by
    rw [show ((29 : ℤ[X])) = ((29 : ℕ) : ℤ[X]) from by norm_num]
    rw [Polynomial.map_natCast]
    exact CharP.cast_eq_zero ((ZMod 29)[X]) 29
  rw [h29, zero_mul, add_zero]

/-- **The monic product recorded in S2132D5FactorizationActual is false.**
Evaluating the constant coefficient gives 12 * 10 = 4 on the left, while the
integer model has constant coefficient 5^12 * 2^36 = 16 modulo 29.  The
missing factor is the reduction 4 of the leading coefficient, so the datum
S2057Mod29FactorizationData cannot be met with this monic quadratic factor;
a scalar multiple of the quadratic (or of the degree-ten factor) is needed. -/
theorem S2132RecordedProduct_false :
    LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual.S2132Factor2 *
        LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual.S2132Factor10 ≠
      LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual.S2132Psi5Z.map
        (Int.castRingHom (ZMod 29)) := by
  intro h
  have h0 := congrArg (Polynomial.eval (0 : ZMod 29)) h
  simp [LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual.S2132Factor2,
    LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual.S2132Factor10,
    LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual.S2132Psi5Z, f] at h0
  exact absurd h0 (by decide)

/-! ## 6b. The mod-29 datum is uninhabitable -/

/-- The constant coefficient of the actual psi_5 over Q.  Computed from the
S1942 formula and the S1667 b-invariants; note the denominator 2^36. -/
theorem S2132Psi5Q_eval_zero :
    S2057Psi5Q.eval 0 = (3814697265625 / 68719476736 : ℚ) := by
  unfold S2057Psi5Q
  rw [S1942_preΨ_five]
  simp only [WeierstrassCurve.preΨ₄, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃,
    S1667Curve_b₂, S1667Curve_b₄, S1667Curve_b₆, S1667Curve_b₈]
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_neg,
    Polynomial.eval_ofNat, Polynomial.eval_natCast, Polynomial.eval_one, Polynomial.eval_zero]
  ring_nf

/-- There is no integer-coefficient polynomial whose base change to Q is the
actual psi_5: the constant coefficient 3814697265625 / 2^36 is not an
integer.  This is the exact reason the integerModel field of
S2057Mod29FactorizationData cannot be filled. -/
theorem S2132NoIntegerModel :
    ¬ ∃ P : ℤ[X], P.map (Int.castRingHom ℚ) = S2057Psi5Q := by
  rintro ⟨P, hP⟩
  have h0 := congrArg (Polynomial.eval (0 : ℚ)) hP
  rw [Polynomial.eval_zero_map, S2132Psi5Q_eval_zero, Int.coe_castRingHom] at h0
  have h0' : ((P.eval 0 : ℤ) : ℚ) = 3814697265625 / 68719476736 := h0
  have hz : ((P.eval 0 : ℤ) : ℚ) * 68719476736 = 3814697265625 := by
    rw [h0']
    norm_num
  have hzZ : (P.eval 0 : ℤ) * 68719476736 = 3814697265625 := by
    exact_mod_cast hz
  have heven : (2 : ℤ) ∣ (P.eval 0) * 68719476736 :=
    dvd_mul_of_dvd_right (by norm_num : (2 : ℤ) ∣ 68719476736) _
  rw [hzZ] at heven
  norm_num at heven

/-- **The S2057 mod-29 factorization datum is uninhabitable.** -/
theorem S2132Mod29FactorizationData_empty :
    ¬ Nonempty S2057Mod29FactorizationData := by
  rintro ⟨D⟩
  exact S2132NoIntegerModel ⟨D.integerModel, D.integerModel_map⟩

/-- **The S2041 remaining input is false as formalized**, because its
factorization half is uninhabitable. -/
theorem S2132S2041Psi5Remaining_false : ¬ S2041Psi5Remaining := by
  rintro ⟨h, _⟩
  exact S2132Mod29FactorizationData_empty h

/-! ## 7. Axiom footprint -/

#print axioms S2132cycleType_permCongr
#print axioms S2132disjoint_permCongr
#print axioms S2132Pair_card_fintype
#print axioms S2132PairEquivS2009
#print axioms S2132PairCycle
#print axioms S2132PairCycle_cycleType
#print axioms S2132PairCycle_exists
#print axioms S2132HasCycleType102_top
#print axioms S2132Psi5L_splits
#print axioms S2132DivisionRoots_card
#print axioms S2132DivisionRootMap
#print axioms S2132DivisionRootEquiv
#print axioms S2132DivisionRootPairEquiv
#print axioms S2132FrobInduces_iff
#print axioms S2132Bridge_of_factorization
#print axioms S2132Bridge_of_factorization_and_honest
#print axioms S2132Psi5Remaining_of_factorization
#print axioms S2132ImageTail_of_cycleType_and_transitive
#print axioms S2132D5LargeImageFive_of_rangeHypotheses
#print axioms S2132D5LargeImageFive_of_rangeData
#print axioms S2132Remaining_of_honest_and_factorization
#print axioms S2132IntegerIdentity
#print axioms S2132CorrectedProduct
#print axioms S2132RecordedProduct_false
#print axioms S2132Psi5Q_eval_zero
#print axioms S2132NoIntegerModel
#print axioms S2132Mod29FactorizationData_empty
#print axioms S2132S2041Psi5Remaining_false

end LeanFormal.IUT.XiFPaper.S2132FrobCycleActual

end
