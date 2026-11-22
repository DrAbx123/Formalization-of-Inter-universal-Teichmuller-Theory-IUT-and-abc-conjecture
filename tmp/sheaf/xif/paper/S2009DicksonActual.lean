/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/

import Mathlib.Tactic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.OrderOfElement

/-!
# S2009: the GL_2(F_5) Dickson/finite-computation interface for the D5 step (5)

This file isolates the group-theoretic part of item (5) of the S1987 report on the
`l = 5` large-image input: Dickson's classification of the proper subgroups of
`GL_2(F_5)` together with the explicit finite verification on the twelve pairs
`{+v}`, `v ∈ F_5^2 ∖ {0}`.

## The object of the finite computation

`S2009Pairs` is the twelve-element set of pairs `{v, -v}` in `F_5^2 ∖ {0}`,
modelled by the canonical representatives whose first nonzero coordinate is `1` or `2`.
`GL_2(F_5)` acts on it through the natural action on vectors, and `pairPermHom`
is the associated monoid homomorphism into `Equiv.Perm S2009Pairs`.

## What is kernel-checked here

* `det_surjective`: the determinant `GL_2(F_5) → (ZMod 5)^*` is surjective
  (Mathlib's `Matrix.GeneralLinearGroup.det_surjective`, restated for the actual group);
* `pairAct_transitive`: `GL_2(F_5)` acts transitively on the twelve pairs;
* `cycleType_pairPerm_g102`: the explicit matrix `!![0, 1; 1, 1]` has cycle type
  `(10, 2)` on the twelve pairs.  The proof uses the explicit enumeration and
  `Equiv.Perm.cycleType_eq`, hence is a genuine kernel computation rather than
  an unchecked native decision procedure;
* `ten_dvd_natCard_of_mem_cycleType102`: any finite subgroup containing an element
  whose pair permutation has cycle type `(10, 2)` has order divisible by `10`;
* `no_cycleType102_of_natCard_96` and `no_cycleType102_of_natCard_48`: a subgroup
  of order `96` or `48` (the orders of the `S_4`- and `S_3 × C_2`-preimages in the
  S1987 report) contains no element of cycle type `(10, 2)`;
* `largeImage_of_dickson`: if the classification statement below holds, then any
  subgroup with surjective determinant, transitive twelve-point action and an element
  of cycle type `(10, 2)` is the whole of `GL_2(F_5)`.

## The exact first missing statement

`S2009DicksonTransitiveClassification` is a plain `Prop`.  It is the exact
group-theoretic finite computation consumed by `largeImage_of_dickson`: every proper
subgroup with surjective determinant and transitive action on the twelve pairs is
contained in a subgroup of order `96` or `48`.  By the S1987 report these two
orders are those of the preimages of `S_4` and `S_3 × C_2` in
`PGL_2(F_5) ≅ S_5`; the Borel (order `80`) is not transitive and the preimage of
`A_5` (order `240`) has determinant image equal to the squares, so the statement is
the precise consequence of Dickson's list needed at `l = 5`.

No inhabitant of `S2009DicksonTransitiveClassification` is produced in this file,
and no extra postulate, unchecked declaration, proof hole, native decision procedure or
vacuous gate is used.
Thus the status is: the reusable interface and the finite computations above are
kernel closed; the classification itself is the exact first missing statement.

## Verification status

The file compiles with `EXIT=0`.  The dependency footprint of every theorem
below is `propext`, `Classical.choice` and `Quot.sound` only; see the
`#print axioms` block at the end.  The missing proposition is not counted as proved.

## Consumers

* S1987D5LargeImageFiveActual (item (5) of the seven gaps in the S1987 report);
* S1993D5FiniteGroupBridgeActual / S1982D5FiveActual, through the large-image clause;
* any later formalisation of the division-field/Galois bridge that needs the
  twelve-point action, the determinant surjectivity or the cycle-type exclusion.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

open Matrix
namespace LeanFormal.IUT.XiFPaper.S2009DicksonActual

abbrev K5 := ZMod 5
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩
abbrev GL2 := GL (Fin 2) K5
abbrev V2 := Fin 2 → K5

abbrev IsRep (v : V2) : Prop :=
  (v 0 = 1 ∨ v 0 = 2) ∨ (v 0 = 0 ∧ (v 1 = 1 ∨ v 1 = 2))
abbrev PairRep := {v : V2 // IsRep v}

/-- The twelve pairs `{v, -v}` of the S1987/S2009 finite computation. -/
abbrev S2009Pairs := PairRep

def normSign (v : V2) : K5 :=
  if v 0 = 1 ∨ v 0 = 2 then 1
  else if v 0 = 3 ∨ v 0 = 4 then -1
  else if v 1 = 1 ∨ v 1 = 2 then 1
  else -1
def normalize (v : V2) : V2 := normSign v • v

theorem normalize_isRep : ∀ v : V2, v ≠ 0 → IsRep (normalize v) := by decide
theorem normalize_eq_or_neg : ∀ v : V2, normalize v = v ∨ normalize v = -v := by decide
theorem normalize_neg : ∀ v : V2, normalize (-v) = normalize v := by decide
theorem normalize_of_isRep : ∀ v : V2, IsRep v → normalize v = v := by decide
theorem isRep_ne_zero : ∀ v : V2, IsRep v → v ≠ 0 := by decide

theorem smul_eq_zero_iff (g : GL2) (v : V2) : g • v = 0 ↔ v = 0 := by
  constructor
  · intro h
    exact Matrix.eq_zero_of_mulVec_eq_zero (Matrix.GeneralLinearGroup.det_ne_zero g) h
  · intro h
    rw [h]; simp

def pairAct (g : GL2) (x : PairRep) : PairRep :=
  ⟨normalize (g • x.1), normalize_isRep (g • x.1) (by
    intro h
    exact isRep_ne_zero x.1 x.2 ((smul_eq_zero_iff g x.1).mp h))⟩

theorem pairAct_one (x : PairRep) : pairAct 1 x = x := by
  apply Subtype.ext
  show normalize (1 • x.1) = x.1
  rw [one_smul, normalize_of_isRep x.1 x.2]

theorem normalize_smul_congr (g : GL2) {v w : V2} (h : w = v ∨ w = -v) :
    normalize (g • w) = normalize (g • v) := by
  rcases h with rfl | rfl
  · rfl
  · rw [show g • (-v) = -(g • v) by simp, normalize_neg]

theorem pairAct_mul (g h : GL2) (x : PairRep) :
    pairAct (g * h) x = pairAct g (pairAct h x) := by
  apply Subtype.ext
  show normalize ((g * h) • x.1) = normalize (g • normalize (h • x.1))
  rw [mul_smul]
  exact (normalize_smul_congr g (normalize_eq_or_neg (h • x.1))).symm

def pairEquiv (g : GL2) : PairRep ≃ PairRep where
  toFun := pairAct g
  invFun := pairAct g⁻¹
  left_inv x := by rw [← pairAct_mul, inv_mul_cancel, pairAct_one]
  right_inv x := by rw [← pairAct_mul, mul_inv_cancel, pairAct_one]

def pairPermHom : GL2 →* Equiv.Perm PairRep where
  toFun g := pairEquiv g
  map_one' := by apply Equiv.ext; intro x; exact pairAct_one x
  map_mul' g h := by apply Equiv.ext; intro x; exact pairAct_mul g h x

def g102 : GL2 := Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; 1, 1] (by decide)

def repList : List PairRep :=
  [⟨![0, 1], by decide⟩,
   ⟨![1, 1], by decide⟩,
   ⟨![1, 2], by decide⟩,
   ⟨![2, 3], by decide⟩,
   ⟨![2, 0], by decide⟩,
   ⟨![0, 2], by decide⟩,
   ⟨![2, 2], by decide⟩,
   ⟨![2, 4], by decide⟩,
   ⟨![1, 4], by decide⟩,
   ⟨![1, 0], by decide⟩,
   ⟨![1, 3], by decide⟩,
   ⟨![2, 1], by decide⟩]

theorem repList_length : repList.length = 12 := by decide
theorem mem_repList : ∀ x : PairRep, x ∈ repList := by decide

def pairOf (i : Fin 12) : PairRep :=
  repList.get ⟨i.1, by rw [repList_length]; exact i.2⟩

def indexOf (x : PairRep) : Fin 12 :=
  ⟨repList.idxOf x, by
    have h := List.idxOf_lt_length_of_mem (mem_repList x)
    rwa [repList_length] at h⟩

theorem indexOf_pairOf : ∀ i : Fin 12, indexOf (pairOf i) = i := by decide
theorem pairOf_indexOf : ∀ x : PairRep, pairOf (indexOf x) = x := by decide

def pairEquivFin : PairRep ≃ Fin 12 where
  toFun := indexOf
  invFun := pairOf
  left_inv := pairOf_indexOf
  right_inv := indexOf_pairOf

theorem isCycle_permCongr {α β : Type*} {e : α ≃ β} {p : Equiv.Perm α}
    (hp : p.IsCycle) : (e.permCongr p).IsCycle := by
  obtain ⟨x, hx, h⟩ := hp
  refine ⟨e x, ?_, ?_⟩
  · intro hc
    apply hx
    have h1 : e (p x) = e x := by
      simpa [Equiv.permCongr_apply] using hc
    exact e.injective h1
  · intro y hy
    have hz : p (e.symm y) ≠ e.symm y := by
      intro hzy
      apply hy
      rw [Equiv.permCongr_apply, hzy, Equiv.apply_symm_apply]
    obtain ⟨n, hn⟩ := h hz
    refine ⟨n, ?_⟩
    have hmap : e.permCongr (p ^ n) = (e.permCongr p) ^ n := by
      simpa using map_zpow (Equiv.permCongrHom e) p n
    calc
      ((e.permCongr p) ^ n) (e x) = e.permCongr (p ^ n) (e x) := by rw [hmap]
      _ = e ((p ^ n) x) := by simp [Equiv.permCongr_apply]
      _ = e (e.symm y) := by rw [hn]
      _ = y := by simp

theorem support_permCongr {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (p : Equiv.Perm α) :
    (e.permCongr p).support = p.support.map e.toEmbedding := by
  ext y
  simp only [Equiv.Perm.mem_support, Finset.mem_map, Equiv.coe_toEmbedding]
  constructor
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    intro h
    apply hy
    rw [Equiv.permCongr_apply, h, Equiv.apply_symm_apply]
  · rintro ⟨x, hx, rfl⟩
    rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
    simpa using hx

theorem card_support_permCongr {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (p : Equiv.Perm α) :
    (e.permCongr p).support.card = p.support.card := by
  rw [support_permCongr]
  exact Finset.card_map _

def tau : Equiv.Perm (Fin 12) :=
  Fin.cycleRange (9 : Fin 12) * Equiv.swap (10 : Fin 12) (11 : Fin 12)

def C10 : Equiv.Perm PairRep := Equiv.permCongr (pairEquivFin.symm) (Fin.cycleRange (9 : Fin 12))
def C2 : Equiv.Perm PairRep := Equiv.permCongr (pairEquivFin.symm) (Equiv.swap (10 : Fin 12) (11 : Fin 12))
def C : Equiv.Perm PairRep := Equiv.permCongr (pairEquivFin.symm) tau

theorem card_support_cycleRange : (Fin.cycleRange (9 : Fin 12)).support.card = 10 := by
  rw [← Equiv.Perm.sum_cycleType, Fin.cycleType_cycleRange (by decide : (9 : Fin 12) ≠ 0)]
  simp

theorem C10_support_card : C10.support.card = 10 := by
  rw [C10, card_support_permCongr, card_support_cycleRange]

theorem C2_support_card : C2.support.card = 2 := by
  rw [C2, card_support_permCongr, Equiv.Perm.card_support_swap (by decide : (10 : Fin 12) ≠ 11)]

theorem C10_isCycle : C10.IsCycle := by
  rw [C10]
  exact isCycle_permCongr (Fin.isCycle_cycleRange (by decide : (9 : Fin 12) ≠ 0))

theorem C2_isCycle : C2.IsCycle := by
  rw [C2]
  exact isCycle_permCongr (Equiv.Perm.isCycle_swap (by decide : (10 : Fin 12) ≠ 11))

theorem pairAct_g102_pairOf : ∀ i : Fin 12, pairAct g102 (pairOf i) = pairOf (tau i) := by decide

theorem C_eq_pairPerm : C = pairPermHom g102 := by
  apply Equiv.ext
  intro x
  have hx : pairOf (indexOf x) = x := pairOf_indexOf x
  have hC : C (pairOf (indexOf x)) = pairOf (tau (indexOf x)) := by
    rw [C, tau]
    simp only [Equiv.permCongr_apply, Equiv.symm_symm]
    have hi : pairEquivFin (pairOf (indexOf x)) = indexOf x := indexOf_pairOf _
    rw [hi]
    rfl
  calc
    C x = C (pairOf (indexOf x)) := by rw [hx]
    _ = pairOf (tau (indexOf x)) := hC
    _ = pairPermHom g102 (pairOf (indexOf x)) := (pairAct_g102_pairOf (indexOf x)).symm
    _ = pairPermHom g102 x := by rw [hx]

theorem disjoint_support_cycleRange_swap :
    Disjoint (Fin.cycleRange (9 : Fin 12)).support (Equiv.swap (10 : Fin 12) (11 : Fin 12)).support := by
  decide

theorem disjoint_C10_C2 : Equiv.Perm.Disjoint C10 C2 := by
  rw [C10, C2, Equiv.Perm.disjoint_iff_disjoint_support, support_permCongr, support_permCongr, Finset.disjoint_map]
  exact disjoint_support_cycleRange_swap

theorem C10_mul_C2 : C10 * C2 = C := by
  rw [C10, C2, C, tau]
  rw [Equiv.permCongr_mul]

theorem cycleType_C : C.cycleType = ({10, 2} : Multiset ℕ) := by
  have hprod : ([C10, C2] : List (Equiv.Perm PairRep)).prod = C := by
    rw [← C10_mul_C2]
    simp
  have hcycle : ∀ σ : Equiv.Perm PairRep, σ ∈ [C10, C2] → σ.IsCycle := by
    intro σ hσ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hσ
    rcases hσ with rfl | rfl
    · exact C10_isCycle
    · exact C2_isCycle
  have hdisj : ([C10, C2] : List (Equiv.Perm PairRep)).Pairwise Equiv.Perm.Disjoint := by
    simp [disjoint_C10_C2]
  have h := Equiv.Perm.cycleType_eq (σ := C) [C10, C2] hprod hcycle hdisj
  rw [h]
  simp [C10_support_card, C2_support_card]
  rfl

theorem cycleType_pairPerm_g102 : (pairPermHom g102).cycleType = ({10, 2} : Multiset ℕ) := by
  rw [← C_eq_pairPerm]
  exact cycleType_C


theorem mulVec_fin_two_local (m : Matrix (Fin 2) (Fin 2) K5) (v : V2) :
    m *ᵥ v = ![m 0 0 * v 0 + m 0 1 * v 1, m 1 0 * v 0 + m 1 1 * v 1] := by
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

def toE0Matrix (v : V2) : Matrix (Fin 2) (Fin 2) K5 :=
  if h : v 0 = 0 then !![0, (v 1)⁻¹; -v 1, 0]
  else !![(v 0)⁻¹, 0; -v 1, v 0]

theorem toE0Matrix_det (v : V2) (hv : v ≠ 0) : (toE0Matrix v).det ≠ 0 := by
  unfold toE0Matrix
  split_ifs with h0
  · have hv1 : v 1 ≠ 0 := by
      intro h1
      apply hv
      funext i
      fin_cases i <;> simp [h0, h1]
    rw [Matrix.det_fin_two]
    simp [hv1]
  · rw [Matrix.det_fin_two]
    simp [h0]

def toE0 (v : V2) (hv : v ≠ 0) : GL2 :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (toE0Matrix v) (toE0Matrix_det v hv)

theorem toE0_smul (v : V2) (hv : v ≠ 0) : toE0 v hv • v = ![1, 0] := by
  ext i
  fin_cases i
  · show (toE0Matrix v *ᵥ v) 0 = (![1, 0] : V2) 0
    unfold toE0Matrix
    split_ifs with h0
    · have hv1 : v 1 ≠ 0 := by
        intro h1
        apply hv
        funext j
        fin_cases j <;> simp [h0, h1]
      rw [mulVec_fin_two_local]
      simp [h0, inv_mul_cancel₀ hv1]
    · rw [mulVec_fin_two_local]
      simp [h0]
  · show (toE0Matrix v *ᵥ v) 1 = (![1, 0] : V2) 1
    unfold toE0Matrix
    split_ifs with h0
    · rw [mulVec_fin_two_local]
      simp [h0]
    · rw [mulVec_fin_two_local]
      simp [h0]
      ring

theorem exists_smul_eq (v w : V2) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ g : GL2, g • v = w := by
  refine ⟨(toE0 w hw)⁻¹ * toE0 v hv, ?_⟩
  rw [mul_smul, toE0_smul v hv]
  have h := toE0_smul w hw
  rw [← h]
  rw [← mul_smul, inv_mul_cancel, one_smul]

theorem pairAct_transitive (x y : PairRep) : ∃ g : GL2, pairAct g x = y := by
  obtain ⟨g, hg⟩ := exists_smul_eq x.1 y.1 (isRep_ne_zero x.1 x.2) (isRep_ne_zero y.1 y.2)
  refine ⟨g, ?_⟩
  apply Subtype.ext
  show normalize (g • x.1) = y.1
  rw [hg, normalize_of_isRep y.1 y.2]


/-! ## Subgroup interfaces -/

def DetSurjectiveOn (H : Subgroup GL2) : Prop :=
  ∀ a : K5ˣ, ∃ h ∈ H, Matrix.GeneralLinearGroup.det h = a

def PairTransitive (H : Subgroup GL2) : Prop :=
  ∀ x y : PairRep, ∃ h ∈ H, pairAct h x = y

def HasCycleType102 (H : Subgroup GL2) : Prop :=
  ∃ h ∈ H, (pairPermHom h).cycleType = ({10, 2} : Multiset ℕ)

theorem detSurjectiveOn_top : DetSurjectiveOn ⊤ := by
  intro a
  obtain ⟨g, hg⟩ := Matrix.GeneralLinearGroup.det_surjective (n := Fin 2) (R := K5) a
  exact ⟨g, trivial, hg⟩

/-- The whole group contains the explicit element of cycle type `(10, 2)`. -/
theorem hasCycleType102_top : HasCycleType102 ⊤ :=
  ⟨g102, trivial, cycleType_pairPerm_g102⟩

theorem pairTransitive_top : PairTransitive ⊤ := by
  intro x y
  obtain ⟨g, hg⟩ := pairAct_transitive x y
  exact ⟨g, trivial, hg⟩

theorem ten_dvd_natCard_of_mem_cycleType102 {H : Subgroup GL2} {h : GL2}
    (hh : h ∈ H) (hc : (pairPermHom h).cycleType = ({10, 2} : Multiset ℕ)) :
    10 ∣ Nat.card H := by
  have horder : orderOf (pairPermHom h) = 10 := by
    rw [← Equiv.Perm.lcm_cycleType, hc]
    decide
  have hdvd1 : 10 ∣ orderOf h := by
    rw [← horder]
    exact orderOf_map_dvd pairPermHom h
  exact hdvd1.trans (Subgroup.orderOf_dvd_natCard H hh)

theorem no_cycleType102_of_five_not_dvd (K : Subgroup GL2)
    (h5 : ¬ 5 ∣ Nat.card K) : ¬ HasCycleType102 K := by
  rintro ⟨h, hh, hc⟩
  exact h5 (dvd_trans (by norm_num : 5 ∣ 10) (ten_dvd_natCard_of_mem_cycleType102 hh hc))

/-- A subgroup of order `96` (the order of the `S_4`-preimage in the S1987 report)
contains no element of cycle type `(10, 2)`. -/
theorem no_cycleType102_of_natCard_96 (K : Subgroup GL2) (hK : Nat.card K = 96) :
    ¬ HasCycleType102 K :=
  no_cycleType102_of_five_not_dvd K (by rw [hK]; norm_num)

/-- A subgroup of order `48` (the order of the `S_3 × C_2`-preimage in the S1987
report) contains no element of cycle type `(10, 2)`. -/
theorem no_cycleType102_of_natCard_48 (K : Subgroup GL2) (hK : Nat.card K = 48) :
    ¬ HasCycleType102 K :=
  no_cycleType102_of_five_not_dvd K (by rw [hK]; norm_num)

/-- **The exact first missing statement.**

Every proper subgroup of `GL_2(F_5)` whose determinant is surjective and whose
action on the twelve pairs is transitive is contained in a subgroup of order
`96` or `48`.  By the S1987 report these orders are those of the preimages in
`GL_2(F_5)` of `S_4` and `S_3 × C_2` under `GL_2(F_5) → PGL_2(F_5) ≅ S_5`
(the kernel is the scalar group `F_5^*` of order `4`).

This is a plain `Prop`: it records the finite Dickson computation without
producing an inhabitant.  The theorem `largeImage_of_dickson` below shows that
it is the exact group-theoretic input needed for the `(10, 2)` exclusion. -/
def S2009DicksonTransitiveClassification : Prop :=
  ∀ H : Subgroup GL2,
    DetSurjectiveOn H → PairTransitive H → H ≠ ⊤ →
      (∃ K : Subgroup GL2, H ≤ K ∧ Nat.card K = 96) ∨
      (∃ K : Subgroup GL2, H ≤ K ∧ Nat.card K = 48)

/-- Readable alias for the first missing statement. -/
abbrev DicksonTransitiveClassification : Prop := S2009DicksonTransitiveClassification

/-- The classification statement is exactly the group-theoretic input needed:
a subgroup with surjective determinant, transitive twelve-point action and an
element of cycle type `(10, 2)` cannot be proper. -/
theorem largeImage_of_dickson (hD : DicksonTransitiveClassification)
    (H : Subgroup GL2) (hdet : DetSurjectiveOn H) (htrans : PairTransitive H)
    (h102 : HasCycleType102 H) : H = ⊤ := by
  by_contra hne
  have h102_of_le : ∀ K : Subgroup GL2, H ≤ K → HasCycleType102 K := by
    intro K hHK
    obtain ⟨h, hh, hc⟩ := h102
    exact ⟨h, hHK hh, hc⟩
  rcases hD H hdet htrans hne with ⟨K, hHK, hK⟩ | ⟨K, hHK, hK⟩
  · exact (no_cycleType102_of_natCard_96 K hK) (h102_of_le K hHK)
  · exact (no_cycleType102_of_natCard_48 K hK) (h102_of_le K hHK)


/-- The exact first missing statement, under the name used in the report. -/
abbrev S2009ExactFirstMissing : Prop := S2009DicksonTransitiveClassification

theorem card_pairRep : Fintype.card PairRep = 12 := by decide
theorem natCard_pairRep : Nat.card PairRep = 12 := by
  rw [Nat.card_eq_fintype_card, card_pairRep]

/-! ## 1. The determinant is surjective -/

theorem det_surjective :
    Function.Surjective (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := K5)) :=
  Matrix.GeneralLinearGroup.det_surjective

theorem natCard_GL2 : Nat.card GL2 = 480 := by
  rw [Matrix.card_GL_field (𝔽 := K5) (n := 2)]
  norm_num [ZMod.card]

/-! ## 2. Axiom audit -/

#print axioms normalize_isRep
#print axioms pairAct_mul
#print axioms pairAct_transitive
#print axioms hasCycleType102_top
#print axioms pairPermHom
#print axioms cycleType_pairPerm_g102
#print axioms ten_dvd_natCard_of_mem_cycleType102
#print axioms no_cycleType102_of_five_not_dvd
#print axioms no_cycleType102_of_natCard_96
#print axioms no_cycleType102_of_natCard_48
#print axioms largeImage_of_dickson
#print axioms natCard_GL2
#print axioms natCard_pairRep
#print axioms det_surjective

end LeanFormal.IUT.XiFPaper.S2009DicksonActual