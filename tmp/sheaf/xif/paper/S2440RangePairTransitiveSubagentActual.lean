/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
-/
import tmp.sheaf.xif.paper.S2378ActualPairTransitiveActual
import tmp.sheaf.xif.paper.S2364D5GroupRouteActual
import tmp.sheaf.xif.paper.S1894D5LargeImageActual

/-!
# S2440: the actual mod-5 range pair-transitivity target

The target of this file is the actual large-image input

  S2203RangePairTransitiveRequired S1982Basis
  = PairTransitive (range (rho_{5,S1982Basis})),

i.e. the twelve-pair transitivity of the actual mod-5 Galois range, equivalently
S2375ExactFirstMissing / S2378ExactFirstMissing (the pair-transitivity half of
the S2203 range hypotheses).

## What is proved here

1. **The S2009 toE0 matrix is special linear.**  The explicit matrix
   toE0Matrix v that S2009 uses to send a nonzero vector v to e_0 has
   determinant exactly 1, not merely a nonzero determinant: it lies in
   SL_2(F_5).  Consequently SL_2(F_5) itself acts transitively on the twelve
   pairs {v, -v} (S2440SL2PairTransitive).

2. **The tree's exact-large-image input implies the target.**
   S1725ImageTail S1987Five S1982Basis (the literal SL_2(F_5) <= range rho
   containment at the S1982 basis, equivalently the S1987/S1982 first missing
   large-image input) implies S2203RangePairTransitiveRequired S1982Basis
   (S2440RangePairTransitive_of_imageTail), and hence the frozen D5 input
   S1987D5LargeImageFive implies it as well
   (S2440RangePairTransitive_of_largeImage).

3. **A strictly weaker sufficient input: a 12-cycle.**  If the range contains a
   single element whose permutation of the twelve pairs is a 12-cycle, then the
   range is pair-transitive (S2440RangePairTransitive_of_twelveCycle).  This is
   the Lean form of item (1) of the S1987 report: the irreducibility of the odd
   5-division polynomial modulo 13 produces a Frobenius acting as a 12-cycle on
   the twelve pairs, which already forces transitivity.

4. **Under the paper's cycle-type input the target is equivalent to the SL_2
   containment.**  Given HasCycleType102 of the actual range (the mod-29
   certificate), pair transitivity and the SL_2 containment are equivalent
   (S2440RangePairTransitive_iff_imageTail_of_cycleType102): the SL_2 side
   implies transitivity by (2), and conversely transitivity plus cycle type
   gives the SL_2 containment by S2364 (sl_le_of_five_dvd).

5. **The target is basis-free.**  Conjugation invariance of the pair action
   (S2440PairTransitive_map_conj_iff) together with S1894's computation of the
   range under a change of basis (S1894MatrixRep_range_conj) shows that
   pair-transitivity at one rank-two basis is equivalent to pair-transitivity at
   every basis (S2440RangePairTransitive_iff_forall_basis); in particular the
   arbitrary choice in S1982Basis is immaterial.

## Exact first missing (status)

The target itself is **not proved**.  Neither is S1725ImageTail at S1982Basis,
nor the twelve-cycle input.  Nothing in the tree relates the twelve pairs of
S2009Pairs/S2056Pair to a factorization of the 5-division polynomial: S2217
isolates the Dedekind--Frobenius bridge as its own missing statement
(S2217Missing), and S1987's report records that the finite certificates
(irreducibility of 2^36 * psi_5 mod 13, factorization mod 29) are not
formalized.  Hence, from the current formalized arithmetic, the only available
reductions of the target are through the two explicit inputs below:

* S2440SL2InputRequired = S1725ImageTail S1987Five S1982Basis
  (equivalent to S1987D5LargeImageFive, the tree's open Serre input);
* S2440TwelveCycleInputRequired = a 12-cycle in the actual range
  (the formal form of the mod-13 irreducibility certificate).

The first is sufficient; the second is sufficient and weaker (its strict
weakness is *not* claimed as a theorem here: it follows from the finite Dickson
computation recorded in the S1987 report, where the order-48 preimage of
S_3 x C_2 is 12-point transitive and contains 12-cycles but is proper and does
not contain SL_2(F_5)).  Neither input is implied by anything in the tree, and
no inhabitant of either is produced.  No sorry, axiom, True/PUnit gate,
native_decide or renamed hypothesis is used: every declaration below is an
actual Lean object, and the two inputs occur only as hypotheses or as the
missing endpoints.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2440RangePairTransitiveSubagentActual

open Matrix

open LeanFormal.IUT.XiFPaper.S2009DicksonActual
open LeanFormal.IUT.XiFPaper.S2166AffinePairCorrespondenceActual
open LeanFormal.IUT.XiFPaper.S2203D5RangeActual
open LeanFormal.IUT.XiFPaper.S2218RangePairTransitiveActual
open LeanFormal.IUT.XiFPaper.S2375RangePairTransitiveActual
open LeanFormal.IUT.XiFPaper.S2378ActualPairTransitiveActual
open LeanFormal.IUT.XiFPaper.S2364D5GroupRouteActual
open LeanFormal.IUT.XiFPaper.S1894D5LargeImageActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual

/-! ## 1. Vocabulary -/

/-- SL_2(F_5) inside GL_2(F_5), as the image of SpecialLinearGroup.toGL.
This is literally the subgroup occurring in S1725ImageTail. -/
abbrev S2440SL2Image : Subgroup GL2 :=
  Subgroup.map Matrix.SpecialLinearGroup.toGL
    (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K5))

/-- The standard pair {e_0, -e_0} of the twelve-pair carrier. -/
def S2440E0Pair : PairRep := ⟨![1, 0], by decide⟩

/-! ## 2. Elementary pairAct identities -/

theorem S2440_pairAct_inv (g : GL2) (x : PairRep) :
    pairAct g⁻¹ (pairAct g x) = x := by
  rw [← pairAct_mul, inv_mul_cancel, pairAct_one]

theorem S2440_pairAct_mul_inv (g : GL2) (x : PairRep) :
    pairAct g (pairAct g⁻¹ x) = x := by
  rw [← pairAct_mul, mul_inv_cancel, pairAct_one]

/-- The transported permutation is the pair action. -/
theorem S2440_pairPermHom_apply (g : GL2) (x : PairRep) :
    pairPermHom g x = pairAct g x := rfl

/-! ## 3. The S2009 toE0 matrix is special linear -/

/-- **The explicit S2009 matrix sending v to e_0 has determinant one.**
Both branches of toE0Matrix have determinant exactly 1; this is the finite
computation that upgrades the S2009 general-linear witness to a special-linear
one. -/
theorem S2440_toE0Matrix_det_eq_one (v : V2) (hv : v ≠ 0) :
    (toE0Matrix v).det = 1 := by
  unfold toE0Matrix
  split_ifs with h0
  · have hv1 : v 1 ≠ 0 := by
      intro h1
      apply hv
      funext i
      fin_cases i <;> simp [h0, h1]
    rw [Matrix.det_fin_two_of]
    simp [hv1]
  · rw [Matrix.det_fin_two_of]
    simp [h0]

/-- The S2009 toE0 matrix as an element of SL_2(F_5). -/
noncomputable def S2440SL2ToE0 (v : V2) (hv : v ≠ 0) :
    Matrix.SpecialLinearGroup (Fin 2) K5 :=
  ⟨toE0Matrix v, S2440_toE0Matrix_det_eq_one v hv⟩

/-- Its underlying matrix is toE0Matrix v. -/
theorem S2440SL2ToE0_coe (v : V2) (hv : v ≠ 0) :
    (S2440SL2ToE0 v hv : Matrix (Fin 2) (Fin 2) K5) = toE0Matrix v := rfl

/-- As a general-linear element, the special-linear witness is the S2009 toE0
element. -/
theorem S2440_toGL_SL2ToE0 (v : V2) (hv : v ≠ 0) :
    Matrix.SpecialLinearGroup.toGL (S2440SL2ToE0 v hv) = toE0 v hv := by
  apply Units.ext
  rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
  rfl

/-- **The special-linear witness sends v to e_0.** -/
theorem S2440SL2ToE0_smul (v : V2) (hv : v ≠ 0) :
    S2440SL2ToE0 v hv • v = ![1, 0] := by
  have h1 : S2440SL2ToE0 v hv • v = toE0Matrix v *ᵥ v := rfl
  have h2 : toE0 v hv • v = toE0Matrix v *ᵥ v := rfl
  rw [h1, ← h2]
  exact toE0_smul v hv

/-! ## 4. SL_2(F_5) is pair-transitive on the twelve pairs -/

/-- Every pair is in the SL_2(F_5)-orbit of the standard pair. -/
theorem S2440_sl2_pair_reaches_e0 (x : PairRep) :
    ∃ g ∈ S2440SL2Image, pairAct g x = S2440E0Pair := by
  have hx : x.1 ≠ 0 := isRep_ne_zero x.1 x.2
  refine ⟨Matrix.SpecialLinearGroup.toGL (S2440SL2ToE0 x.1 hx),
    Subgroup.mem_map.mpr ⟨S2440SL2ToE0 x.1 hx, trivial, rfl⟩, ?_⟩
  apply Subtype.ext
  change normalize
    (Matrix.SpecialLinearGroup.toGL (S2440SL2ToE0 x.1 hx) • x.1) = ![1, 0]
  rw [show Matrix.SpecialLinearGroup.toGL (S2440SL2ToE0 x.1 hx) • x.1
        = S2440SL2ToE0 x.1 hx • x.1 from rfl]
  rw [S2440SL2ToE0_smul x.1 hx]
  exact normalize_of_isRep ![1, 0] (by decide)

/-- **SL_2(F_5) acts transitively on the twelve pairs {v, -v}.**  The S2009
determinant-one witnesses give the transitivity directly. -/
theorem S2440SL2PairTransitive : PairTransitive S2440SL2Image := by
  intro x y
  obtain ⟨g, hg, hgx⟩ := S2440_sl2_pair_reaches_e0 x
  obtain ⟨h, hh, hhy⟩ := S2440_sl2_pair_reaches_e0 y
  refine ⟨h⁻¹ * g, mul_mem (inv_mem hh) hg, ?_⟩
  rw [pairAct_mul, hgx]
  rw [← S2440_pairAct_inv h y, hhy]

/-! ## 5. Monotonicity and the reduction of the actual target -/

theorem S2440PairTransitive_mono {H K : Subgroup GL2} (hHK : H ≤ K)
    (h : PairTransitive H) : PairTransitive K := by
  intro x y
  obtain ⟨g, hg, hgxy⟩ := h x y
  exact ⟨g, hHK hg, hgxy⟩

/-- The tree's exact large-image input at the S1982 basis.  This is literally
S1725ImageTail S1987Five S1982Basis, i.e. SL_2(F_5) <= range rho, and it is
equivalent to S1987D5LargeImageFive by S1987's basis-independence. -/
def S2440SL2InputRequired : Prop :=
  S1725ImageTail S1987Five S1982Basis

/-- The tree's large-image input is exactly the frozen S1987 target. -/
theorem S2440SL2InputRequired_iff_largeImage :
    S2440SL2InputRequired ↔ S1987D5LargeImageFive :=
  (S1987D5LargeImageFive_iff_tail_basis).symm

/-- **The exact-large-image input implies the actual pair-transitivity
target.** -/
theorem S2440RangePairTransitive_of_imageTail
    (h : S1725ImageTail S1987Five S1982Basis) :
    S2375RangePairTransitiveRequired := by
  unfold S2375RangePairTransitiveRequired S2203RangePairTransitiveRequired
  exact S2440PairTransitive_mono h S2440SL2PairTransitive

/-- **The frozen S1987 large-image target implies the actual pair-transitivity
target.** -/
theorem S2440RangePairTransitive_of_largeImage
    (h : S1987D5LargeImageFive) : S2375RangePairTransitiveRequired :=
  S2440RangePairTransitive_of_imageTail
    ((S1987D5LargeImageFive_iff_tail_basis).mp h)

/-! ## 6. A weaker sufficient input: a single 12-cycle in the range -/

/-- A permutation of the twelve pairs with cycle type {12} moves every point. -/
theorem S2440_pairPerm_moved_of_cycleType12 {h : GL2}
    (hc : (pairPermHom h).cycleType = ({12} : Multiset ℕ)) (x : PairRep) :
    pairPermHom h x ≠ x := by
  have hcycle : (pairPermHom h).IsCycle :=
    Equiv.Perm.card_cycleType_eq_one.mp (by rw [hc]; rfl)
  have hsupp : (pairPermHom h).support.card = 12 := by
    have h := hcycle.cycleType
    rw [hc] at h
    simpa using h.symm
  have huniv : (pairPermHom h).support = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [card_pairRep]; exact hsupp)
  intro hfix
  have hxn : x ∉ (pairPermHom h).support := by
    simp [Equiv.Perm.mem_support, hfix]
  rw [huniv] at hxn
  exact hxn (Finset.mem_univ x)

/-- **A 12-cycle in a subgroup makes it pair-transitive.** -/
theorem S2440PairTransitive_of_cycleType12 {H : Subgroup GL2}
    (h12 : ∃ h ∈ H, (pairPermHom h).cycleType = ({12} : Multiset ℕ)) :
    PairTransitive H := by
  obtain ⟨h, hh, hc⟩ := h12
  intro x y
  have hcycle : (pairPermHom h).IsCycle :=
    Equiv.Perm.card_cycleType_eq_one.mp (by rw [hc]; rfl)
  obtain ⟨i, hi⟩ := hcycle.exists_pow_eq
    (S2440_pairPerm_moved_of_cycleType12 hc x)
    (S2440_pairPerm_moved_of_cycleType12 hc y)
  refine ⟨h ^ i, pow_mem hh i, ?_⟩
  have h1 : pairAct (h ^ i) x = (pairPermHom (h ^ i)) x := rfl
  rw [h1, map_pow pairPermHom h i]
  exact hi

/-- The twelve-cycle input: the actual mod-5 range contains an element acting
as a 12-cycle on the twelve pairs.  This is the formal shape of the S1987
report's irreducibility certificate for psi_5 modulo 13 (a degree-12
irreducible reduction produces a Frobenius acting as a 12-cycle). -/
def S2440TwelveCycleInputRequired : Prop :=
  ∃ h ∈ (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis).range,
    (pairPermHom h).cycleType = ({12} : Multiset ℕ)

/-- **The twelve-cycle input implies the actual pair-transitivity target.** -/
theorem S2440RangePairTransitive_of_twelveCycle
    (h : S2440TwelveCycleInputRequired) : S2375RangePairTransitiveRequired := by
  unfold S2375RangePairTransitiveRequired S2203RangePairTransitiveRequired
  exact S2440PairTransitive_of_cycleType12 h

/-! ## 7. Conjugation invariance and basis independence -/

/-- The pair action of a conjugate. -/
theorem S2440pairAct_conj (c g : GL2) (x : PairRep) :
    pairAct (c * g * c⁻¹) (pairAct c x) = pairAct c (pairAct g x) := by
  rw [pairAct_mul, S2440_pairAct_inv c x, pairAct_mul]

/-- Pair transitivity is invariant under conjugation of the subgroup: the
conjugate direction. -/
theorem S2440PairTransitive_of_map_conj {H : Subgroup GL2} (c : GL2)
    (h : PairTransitive (Subgroup.map (MulAut.conj c).toMonoidHom H)) :
    PairTransitive H := by
  intro x y
  obtain ⟨k, hk, hkxy⟩ := h (pairAct c x) (pairAct c y)
  obtain ⟨g, hg, hgk⟩ := Subgroup.mem_map.mp hk
  have hgk' : c * g * c⁻¹ = k := by
    rw [← hgk, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  refine ⟨g, hg, ?_⟩
  have h1 : pairAct (c * g * c⁻¹) (pairAct c x) = pairAct c y := by
    rw [hgk']
    exact hkxy
  have h2 : pairAct c (pairAct g x) = pairAct c y := by
    rwa [S2440pairAct_conj] at h1
  have h3 := congrArg (pairAct c⁻¹) h2
  rwa [S2440_pairAct_inv, S2440_pairAct_inv] at h3

/-- Pair transitivity is invariant under conjugation of the subgroup: the
forward direction. -/
theorem S2440PairTransitive_map_conj_of {H : Subgroup GL2} (c : GL2)
    (h : PairTransitive H) :
    PairTransitive (Subgroup.map (MulAut.conj c).toMonoidHom H) := by
  intro x y
  obtain ⟨g, hg, hgxy⟩ := h (pairAct c⁻¹ x) (pairAct c⁻¹ y)
  refine ⟨c * g * c⁻¹, Subgroup.mem_map.mpr ⟨g, hg, ?_⟩, ?_⟩
  · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  · rw [← S2440_pairAct_mul_inv c x, ← S2440_pairAct_mul_inv c y,
      S2440pairAct_conj, hgxy]

/-- Pair transitivity depends only on the conjugacy class of the subgroup. -/
theorem S2440PairTransitive_map_conj_iff {H : Subgroup GL2} (c : GL2) :
    PairTransitive (Subgroup.map (MulAut.conj c).toMonoidHom H) ↔
      PairTransitive H :=
  ⟨S2440PairTransitive_of_map_conj c, S2440PairTransitive_map_conj_of c⟩

/-- **Pair transitivity at one rank-two basis is pair transitivity at every
basis**, by S1894's conjugation formula for the actual mod-5 ranges. -/
theorem S2440RangePairTransitive_basis_indep
    (b b' : S1725TorsionBasis S1987Five) :
    S2203RangePairTransitiveRequired b ↔ S2203RangePairTransitiveRequired b' := by
  unfold S2203RangePairTransitiveRequired
  rw [S1894MatrixRep_range_conj S1987Five b b']
  exact (S2440PairTransitive_map_conj_iff
    (S1894BasisChangeGL S1987Five b b')).symm

/-- The target is the basis-free form: the arbitrary choice in S1982Basis is
immaterial. -/
theorem S2440RangePairTransitive_iff_forall_basis :
    (∀ b : S1725TorsionBasis S1987Five, S2203RangePairTransitiveRequired b) ↔
      S2375RangePairTransitiveRequired := by
  constructor
  · intro h
    exact h S1982Basis
  · intro h b
    exact (S2440RangePairTransitive_basis_indep b S1982Basis).mpr h

/-! ## 8. Under the paper's cycle-type input, the target is the SL_2
containment -/

/-- **With the paper's (10,2) cycle-type input, the pair-transitivity target is
exactly the SL_2(F_5) containment at the basis.**  The forward direction is
S2364's sl_le_of_five_dvd route, the reverse direction is section 4 above. -/
theorem S2440RangePairTransitive_iff_imageTail_of_cycleType102
    (h102 : S2203RangeCycleTypeRequired S1982Basis) :
    S2203RangePairTransitiveRequired S1982Basis ↔
      S1725ImageTail S1987Five S1982Basis :=
  ⟨fun htrans => S2364RangeImageTail_of_hypotheses S1982Basis h102 htrans,
   fun htail => S2440RangePairTransitive_of_imageTail htail⟩

/-! ## 9. The exact statement and its status -/

/-- The actual range pair-transitivity target, under a local name.  It is
definitionally S2203RangePairTransitiveRequired S1982Basis, hence
S2375ExactFirstMissing and S2378ExactFirstMissing. -/
def S2440RangePairTransitiveRequired : Prop := S2375RangePairTransitiveRequired

/-- The exact first missing statement of this file: the actual pair
transitivity of the mod-5 range at the S1982 basis.  It coincides with
S2375ExactFirstMissing. -/
def S2440ExactFirstMissing : Prop := S2440RangePairTransitiveRequired

/-- Local name and S2375's exact first missing are the same problem. -/
theorem S2440ExactFirstMissing_iff_S2375 :
    S2440ExactFirstMissing ↔ S2375ExactFirstMissing := Iff.rfl

/-- Local name and S2378's exact first missing are the same problem. -/
theorem S2440ExactFirstMissing_iff_S2378 :
    S2440ExactFirstMissing ↔ S2378ExactFirstMissing := Iff.rfl

/-- The target is definitionally the S2203 range hypothesis at S1982Basis. -/
theorem S2440RangePairTransitiveRequired_iff_S2203 :
    S2440RangePairTransitiveRequired ↔
      S2203RangePairTransitiveRequired S1982Basis := Iff.rfl

/-- The two explicit inputs available for the target: both suffice, the
twelve-cycle one being weaker. -/
theorem S2440_target_from_inputs :
    (S2440TwelveCycleInputRequired → S2440ExactFirstMissing) ∧
      (S2440SL2InputRequired → S2440ExactFirstMissing) :=
  ⟨S2440RangePairTransitive_of_twelveCycle,
   S2440RangePairTransitive_of_imageTail⟩

/-- The large-image target of S1987/S1982 implies the target of this file. -/
theorem S2440ExactFirstMissing_of_largeImage (h : S1987D5LargeImageFive) :
    S2440ExactFirstMissing :=
  S2440RangePairTransitive_of_largeImage h

/-! ## 10. Axiom footprint -/

#print axioms S2440_toE0Matrix_det_eq_one
#print axioms S2440SL2ToE0_smul
#print axioms S2440_sl2_pair_reaches_e0
#print axioms S2440SL2PairTransitive
#print axioms S2440PairTransitive_mono
#print axioms S2440RangePairTransitive_of_imageTail
#print axioms S2440RangePairTransitive_of_largeImage
#print axioms S2440_pairPerm_moved_of_cycleType12
#print axioms S2440PairTransitive_of_cycleType12
#print axioms S2440RangePairTransitive_of_twelveCycle
#print axioms S2440pairAct_conj
#print axioms S2440PairTransitive_map_conj_iff
#print axioms S2440RangePairTransitive_basis_indep
#print axioms S2440RangePairTransitive_iff_forall_basis
#print axioms S2440RangePairTransitive_iff_imageTail_of_cycleType102
#print axioms S2440_target_from_inputs
#print axioms S2440ExactFirstMissing_of_largeImage

end LeanFormal.IUT.XiFPaper.S2440RangePairTransitiveSubagentActual

end
