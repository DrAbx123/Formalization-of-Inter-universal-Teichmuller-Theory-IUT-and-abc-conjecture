/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import tmp.sheaf.xif.paper.S1413SourceKPlaceQComparisonActual
import tmp.sheaf.xif.paper.S342QVFamilyRootImpossibleActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnits
import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# S2092: the paper `O^⊿` carrier and the paper `q_v` attachment at the paper's
designated K-place

Layer: O (IUT I, Example 3.2(iv); the S2040 paper O^tri / q_v / O^×μ attachment).

## What the paper says

* IUT I, §0 (Fig. I1.2 notation):
  `O^⊿` is the *multiplicative monoid of nonzero integral elements* of the local
  field, and the `F`-prime-strip at `v ∈ V` is modelled by `G_v ↷ O^⊿_{F̄_v}`.
* IUT I, Example 3.2(iv) (corpus lines 3701–3726):
  `q_v ∈ O^⊿(T_{X_v}) (≅ O^⊿_{K_v})`; `q_v` admits a `2l`-th root
  `q_v^{1/2l} ∈ O^⊿(T_{X_v})`, determined up to a `μ_{2l}(T_{X_v})`-multiple.
  The paper derives the existence of the root from Definition 3.1(b)
  (`2·3`-torsion rational over `F`, hence `q_v` is a square in `K_v`) together
  with Definition 3.1(c) (`K = F(E[l])`, hence `q_v` is an `l`-th power in `K_v`).

## What this file constructs (all kernel-checked, no `sorry`)

1. The paper's `O^⊿` carrier `paperOtriSubmonoid K` (nonzero integral elements),
   instantiated at the paper's **designated K-place** `sectionKPlace T b` of S1413
   (the Definition 3.1(e) section lift of the bad moduli place `b`).  This is the
   same monoid as S2032's `localOFieldIntegralSubmonoid` (there over
   `AlgebraicClosure ℚ_[p]`) and S60's `oBoundaryMonoid` (there over a completion),
   stated for the actual completion at the paper's place.
2. The paper `q_v`: `paperQV` is S1413's actual `sectionQ`, i.e. the completion
   image of the clause-B source q-parameter under the section, proved to be a
   nonzero integral non-unit of the carrier (`q_v ∈ O^⊿`, `‖q_v‖ < 1`), with the
   source attachment `paperQV = completionMap (shadowQ)`.
3. The `O^×`/`O^×μ` attachment: `paperOUnits = (Integers K_v)^×`,
   `paperOUnitsMu = rootsOfUnity (2l) (Integers K_v)`, the actual `O^× → O^⊿`
   injection `paperOUnitsToOtri` (proved injective), and the `2l`-exponent law
   for `O^×μ`.  The ratio of any two `2l`-th roots of `q_v` in the completion is
   proved to lie in `O^×μ` (`paperRootRatio_mem_mu`): the paper's `μ_{2l}`
   indeterminacy law for the (missing) root.
4. The existence of a `2l`-th root in the **algebraic closure** of `K_v`
   (`paperClosureRoot`) and the pure-field indeterminacy law: any two such roots
   differ by a `2l`-th root of unity.  Thus the missing datum is precisely the
   `K_v`-`rationality` of the root, not the existence of an abstract root.

## The exact first missing

`paperOtriRootMissing T b` (= S1413's `SectionTwoLRoot`): a `2l`-th root of
`q_v` **inside the completion** `K_v`, i.e. the paper's
`q_v^{1/2l} ∈ O^⊿(T_{X_v}) ≅ O^⊿_{K_v}` of Example 3.2(iv).  It is equivalent
to the carrier-level root `paperOtriRootInCompletion` and it forces
`l ∣ eSource` (S1413) and `2l ∣ ord(q_v)`.  The paper's two torsion inputs
(Definition 3.1(b),(c)) are not formalized: the tree has the torsion rationality
(`T.clauseC.torsion23_rational`) and the kernel-field identification
(`T.clauseC.kernel_field_identification`), but no Tate-curve description of the
torsion points `q_v^{1/2}`, `q_v^{1/l}`, and the repo's `q_v` is the F-side
clause-B parameter with order prime to `l` (S342: no completion root), so the
paper's root must live at the K-place, where it is exactly the missing datum.

## No fake, no all-units, no qVFamily

* The carrier is the paper's `O^⊿`, not `⊤`/`PUnit` and not the unit group; the
  q_v is the actual completion image of the source q-parameter, not an arbitrary
  element; `O^×μ` is `rootsOfUnity (2l)`, not all units.
* `no_completionMonoidEval_of_Fside_qVFamily`: no monoid evaluation to the F-side
  completion can send a q-section with a root section to the F-side `qVFamily`
  (S342/S2057).  So the F-side `qVFamily` is *not* the paper `q_v`; the paper
  `q_v` is the K-side base change `sectionQ` constructed here.
* The S346/`S357` orbifold carrier spec is not used as the paper carrier: its
  `qSection_toCompletion` is a bare function (vacuous to inhabit); the faithful
  monoid-hom form is exactly what is proved impossible above.

No `sorry`, `axiom`, `True`/`PUnit` slot, empty type, arbitrary inhabitant or
assumption-only gate is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2092PaperOtriActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.XiFPaper.S1413SourceKPlaceQComparisonActual
open LeanFormal.IUT.XiFPaper.S342QVFamilyRootImpossibleActual
open LeanFormal.IUT.XiFPaper.TwoLthRootQVActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (N8Closure.nativePlaceSelection T))

/-! ## 1. The paper `O^⊿` carrier -/

/-- The paper's `O^⊿`: the multiplicative monoid of nonzero integral elements of a
nonarchimedean local field (IUT I, §0; Example 3.2(iv): `O^⊿(T_{X_v}) ≅ O^⊿_{K_v}`).
S2032 states the same monoid over the `Q_p`-model `AlgebraicClosure ℚ_[p]`; S60
states it over a completion.  Here it is stated for the actual completion at the
paper's designated K-place. -/
noncomputable def paperOtriSubmonoid (K : Type) [NormedField K] [IsUltrametricDist K] :
    Submonoid K where
  carrier := {x | ‖x‖ ≤ 1 ∧ x ≠ 0}
  one_mem' := ⟨by simp, one_ne_zero⟩
  mul_mem' := by
    intro x y hx hy
    refine ⟨?_, mul_ne_zero hx.2 hy.2⟩
    rw [norm_mul]
    calc ‖x‖ * ‖y‖ ≤ 1 * 1 := mul_le_mul hx.1 hy.1 (norm_nonneg y) zero_le_one
      _ = 1 := by ring

/-- The completed local field `K_v` at the paper's designated K-place. -/
abbrev paperKv : Type := Completion (sectionKPlace T b)

/-- The paper's `O^⊿` carrier at the designated K-place. -/
abbrev paperOtri : Submonoid (paperKv T b) := paperOtriSubmonoid (paperKv T b)

theorem paperOtri_mem_iff (x : paperKv T b) :
    x ∈ paperOtri T b ↔ ‖x‖ ≤ 1 ∧ x ≠ 0 := Iff.rfl

/-! ## 2. The paper `q_v` -/

theorem twoL_pos (l : PrimeGeFive) : 0 < 2 * l.value :=
  Nat.mul_pos (by norm_num) l.prime.pos

/-- The paper `q_v` at the designated K-place is the actual `sectionQ` (S1413):
the completion image of the clause-B source q-parameter under the source section.
It is a nonzero integral element of `O^⊿` (`IUT I`, Example 3.2(iv)). -/
noncomputable def paperQV : paperOtri T b := by
  refine ⟨(sectionQ T b).q, le_of_lt ?_, (sectionQ T b).q_ne_zero⟩
  rw [Valued.toNormedField.norm_lt_one_iff]
  exact (sectionQ T b).valuation_lt_one

@[simp] theorem paperQV_val : (paperQV T b : paperKv T b) = (sectionQ T b).q := rfl

theorem paperQV_norm_lt_one : ‖(paperQV T b : paperKv T b)‖ < 1 := by
  rw [paperQV_val, Valued.toNormedField.norm_lt_one_iff]
  exact (sectionQ T b).valuation_lt_one

theorem paperQV_norm_ne_one : ‖(paperQV T b : paperKv T b)‖ ≠ 1 :=
  ne_of_lt (paperQV_norm_lt_one T b)

/-- The source attachment: the paper `q_v` is the completion image of the clause-B
q-parameter `shadowQ` at the F-place under the source section. -/
theorem paperQV_eq_completionMap :
    (paperQV T b : paperKv T b) = completionMapSection T b (shadowQ T b).q :=
  sectionQ_q T b

/-- The order law at the paper's place: `ord(q_v) = e · ord(q)` with `e` the
source section ramification index (S1413). -/
theorem paperQV_order :
    (sectionQ T b).order = eSource T b * (shadowQ T b).order :=
  sectionQ_order T b

/-- The F-side order is prime to `l` (clause (c), S1413). -/
theorem paperQ_shadowOrder_coprime : Nat.Coprime (shadowQ T b).order l.value :=
  shadowQ_order_coprime T b

/-! ## 3. The `O^×` / `O^×μ` attachment -/

/-- The actual `O^×` of the completed local field: the units of the valuation ring
of the norm (`S1978`'s carrier, at the paper's place). -/
abbrev paperOUnits : Type := (Integers (paperKv T b))ˣ

/-- The actual `O^×μ`: the `2l`-th roots of unity in the integral units,
`μ_{2l}(T_{X_v})` of IUT I, Example 3.2(iv).  This is *not* the full unit group. -/
abbrev paperOUnitsMu : Subgroup (paperOUnits T b) :=
  rootsOfUnity (2 * l.value) (Integers (paperKv T b))

theorem paperOUnitsMu_pow (ζ : paperOUnitsMu T b) :
    (ζ : paperOUnits T b) ^ (2 * l.value) = 1 := by
  simpa using (mem_rootsOfUnity (2 * l.value) (ζ : paperOUnits T b)).mp ζ.2

/-- The actual `O^× → O^⊿` inclusion (integral units are nonzero integral
elements). -/
noncomputable def paperOUnitsToOtri : paperOUnits T b →* paperOtri T b where
  toFun u :=
    ⟨(u.val : paperKv T b), by
      refine ⟨?_, ?_⟩
      · rw [norm_unit_eq_one u]
      · intro hzero
        exact Units.ne_zero u (by apply Subtype.ext; exact hzero)⟩
  map_one' := by ext; rfl
  map_mul' := by intro u v; ext; rfl

theorem paperOUnitsToOtri_injective : Function.Injective (paperOUnitsToOtri T b) := by
  intro u v h
  have h' : (u.val : paperKv T b) = (v.val : paperKv T b) :=
    congrArg (fun z : paperOtri T b => (z : paperKv T b)) h
  apply Units.ext
  apply Subtype.ext
  exact h'

/-- The paper's `q_v` is not an integral unit: its norm is `< 1`, while integral
units have norm `1`.  So the paper's `q_v` genuinely needs `O^⊿`, not `O^×`
(the S2032 observation, at the paper's place). -/
theorem paperQV_ne_paperOUnits_val (u : paperOUnits T b) :
    (u.val : paperKv T b) ≠ (paperQV T b : paperKv T b) := by
  intro h
  have hone : ‖(u.val : paperKv T b)‖ = 1 := norm_unit_eq_one u
  rw [h] at hone
  exact paperQV_norm_ne_one T b hone

/-! ## 4. The `μ_{2l}` indeterminacy of a completion root -/

theorem paperRootNorm_eq {r1 r2 : paperKv T b}
    (h1 : r1 ^ (2 * l.value) = (sectionQ T b).q)
    (h2 : r2 ^ (2 * l.value) = (sectionQ T b).q) : ‖r1‖ = ‖r2‖ := by
  have h1p : ‖r1‖ ^ (2 * l.value) = ‖(sectionQ T b).q‖ := by rw [← norm_pow, h1]
  have h2p : ‖r2‖ ^ (2 * l.value) = ‖(sectionQ T b).q‖ := by rw [← norm_pow, h2]
  exact (pow_left_inj₀ (norm_nonneg r1) (norm_nonneg r2)
    (show 2 * l.value ≠ 0 from Nat.mul_ne_zero (by norm_num) (Nat.Prime.ne_zero l.2))).mp
    (h1p.trans h2p.symm)

theorem paperRootRatio_norm_one {r1 r2 : paperKv T b}
    (h1 : r1 ^ (2 * l.value) = (sectionQ T b).q)
    (h2 : r2 ^ (2 * l.value) = (sectionQ T b).q) : ‖r1 / r2‖ = 1 := by
  have hr2 : r2 ≠ 0 := by
    intro h
    rw [h, zero_pow (show 2 * l.value ≠ 0 from
      Nat.mul_ne_zero (by norm_num) (Nat.Prime.ne_zero l.2))] at h2
    exact (sectionQ T b).q_ne_zero h2.symm
  have hnorm2 : ‖r2‖ ≠ 0 := by
    intro h
    exact hr2 (norm_eq_zero.mp h)
  rw [norm_div, paperRootNorm_eq T b h1 h2]
  exact div_self hnorm2

/-- The ratio of two `2l`-th roots of `q_v` in the completion is an actual
integral unit (an element of `O^×`). -/
noncomputable def paperRootRatio {r1 r2 : paperKv T b}
    (h1 : r1 ^ (2 * l.value) = (sectionQ T b).q)
    (h2 : r2 ^ (2 * l.value) = (sectionQ T b).q) : paperOUnits T b :=
  unitOfNormOne ⟨r1 / r2, paperRootRatio_norm_one T b h1 h2⟩

theorem paperRootRatio_val {r1 r2 : paperKv T b}
    (h1 : r1 ^ (2 * l.value) = (sectionQ T b).q)
    (h2 : r2 ^ (2 * l.value) = (sectionQ T b).q) :
    ((paperRootRatio T b h1 h2).val : paperKv T b) = r1 / r2 := rfl

theorem paperRootRatio_pow {r1 r2 : paperKv T b}
    (h1 : r1 ^ (2 * l.value) = (sectionQ T b).q)
    (h2 : r2 ^ (2 * l.value) = (sectionQ T b).q) :
    (paperRootRatio T b h1 h2) ^ (2 * l.value) = 1 := by
  apply Units.ext
  apply Subtype.ext
  show ((paperRootRatio T b h1 h2).val : paperKv T b) ^ (2 * l.value) = 1
  rw [paperRootRatio_val T b h1 h2, div_pow, h1, h2,
    div_self (sectionQ T b).q_ne_zero]

/-- **The paper's `μ_{2l}(T_{X_v})` indeterminacy law** for the root of
Example 3.2(iv): the ratio of two `2l`-th roots of `q_v` lies in
`O^×μ = μ_{2l}`. -/
theorem paperRootRatio_mem_mu {r1 r2 : paperKv T b}
    (h1 : r1 ^ (2 * l.value) = (sectionQ T b).q)
    (h2 : r2 ^ (2 * l.value) = (sectionQ T b).q) :
    paperRootRatio T b h1 h2 ∈ paperOUnitsMu T b := by
  rw [mem_rootsOfUnity]
  exact paperRootRatio_pow T b h1 h2

/-! ## 5. The root in the algebraic closure of `K_v` -/

/-- An algebraic closure of `K_v` (the paper's `F̄_v`). -/
abbrev paperClosure : Type := AlgebraicClosure (paperKv T b)

theorem paperClosureQV_ne_zero :
    algebraMap (paperKv T b) (paperClosure T b) (sectionQ T b).q ≠ 0 := by
  let u : (paperKv T b)ˣ := Units.mk0 (sectionQ T b).q (sectionQ T b).q_ne_zero
  have h : algebraMap (paperKv T b) (paperClosure T b) (sectionQ T b).q =
      ((Units.map (algebraMap (paperKv T b) (paperClosure T b)).toMonoidHom
        u : (paperClosure T b)ˣ) : paperClosure T b) := rfl
  rw [h]
  exact Units.ne_zero _

/-- A `2l`-th root of the paper `q_v` in the algebraic closure `F̄_v`.  This is
the §0 carrier; it always exists because `F̄_v` is algebraically closed. -/
noncomputable def paperClosureRoot : paperClosure T b :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq
    (algebraMap (paperKv T b) (paperClosure T b) (sectionQ T b).q) (twoL_pos l))

theorem paperClosureRoot_pow :
    paperClosureRoot T b ^ (2 * l.value) =
      algebraMap (paperKv T b) (paperClosure T b) (sectionQ T b).q :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq
    (algebraMap (paperKv T b) (paperClosure T b) (sectionQ T b).q) (twoL_pos l))

/-- In the algebraic closure, any two `2l`-th roots of `q_v` differ by a `2l`-th
root of unity (the field form of the `μ_{2l}` indeterminacy). -/
theorem paperClosureRoot_ratio_pow_one {r1 r2 : paperClosure T b}
    (h1 : r1 ^ (2 * l.value) =
      algebraMap (paperKv T b) (paperClosure T b) (sectionQ T b).q)
    (h2 : r2 ^ (2 * l.value) =
      algebraMap (paperKv T b) (paperClosure T b) (sectionQ T b).q) :
    (r1 / r2) ^ (2 * l.value) = 1 := by
  rw [div_pow, h1, h2, div_self (paperClosureQV_ne_zero T b)]

/-! ## 6. The exact first missing: the root inside the completion `K_v` -/

/-- A `2l`-th root of `q_v` inside the paper's `O^⊿` carrier at the designated
K-place, i.e. the paper's `q_v^{1/2l} ∈ O^⊿(T_{X_v}) ≅ O^⊿_{K_v}`. -/
def paperOtriRootInCompletion : Prop :=
  ∃ r : paperOtri T b, (r : paperKv T b) ^ (2 * l.value) = (sectionQ T b).q

/-- **The exact first missing**, by name: S1413's `SectionTwoLRoot` — a `2l`-th
root of the paper `q_v` in the specified completion.  This is the paper's
Example 3.2(iv) assertion `q_v^{1/2l} ∈ O^⊿(T_{X_v}) ≅ O^⊿_{K_v}`. -/
def paperOtriRootMissing : Prop := SectionTwoLRootRequired (T := T) (b := b)

/-- The missing root is exactly the carrier-level root. -/
theorem paperOtriRootMissing_iff :
    paperOtriRootMissing T b ↔ paperOtriRootInCompletion T b := by
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨⟨r, ?_⟩, hr⟩
    refine ⟨?_, ?_⟩
    · by_contra hle
      have hgt : 1 < ‖r‖ := not_le.mp hle
      have hpow : ‖r‖ ^ (2 * l.value) = ‖(sectionQ T b).q‖ := by
        rw [← norm_pow, hr]
      have hlt : ‖(sectionQ T b).q‖ < 1 := by
        rw [Valued.toNormedField.norm_lt_one_iff]
        exact (sectionQ T b).valuation_lt_one
      have h1 : 1 < ‖r‖ ^ (2 * l.value) :=
        one_lt_pow₀ hgt (show 2 * l.value ≠ 0 from
          Nat.mul_ne_zero (by norm_num) (Nat.Prime.ne_zero l.2))
      rw [hpow] at h1
      linarith
    · intro hzero
      rw [hzero, zero_pow (show 2 * l.value ≠ 0 from
        Nat.mul_ne_zero (by norm_num) (Nat.Prime.ne_zero l.2))] at hr
      exact (sectionQ T b).q_ne_zero hr.symm
  · rintro ⟨r, hr⟩
    exact ⟨((r : paperKv T b)), hr⟩

/-- The missing root is exactly the paper's `q_v^{1/2l}`: a `2l`-th root of the
constructed `paperQV` inside the `O^⊿` carrier. -/
theorem paperOtriRootInCompletion_iff_paperQV :
    paperOtriRootInCompletion T b ↔
      ∃ r : paperOtri T b,
        (r : paperKv T b) ^ (2 * l.value) = (paperQV T b : paperKv T b) := by
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨r, by rwa [paperQV_val]⟩
  · rintro ⟨r, hr⟩
    exact ⟨r, by rwa [paperQV_val] at hr⟩

/-- A root in the paper's carrier forces `l ∣ eSource` (S1413's arithmetic
obstruction at the paper's place). -/
theorem paperOtriRoot_forces_l_dvd_ramification (r : paperOtri T b)
    (hr : (r : paperKv T b) ^ (2 * l.value) = (sectionQ T b).q) :
    l.value ∣ eSource T b :=
  l_dvd_ramification_of_root T b (r : paperKv T b) hr

/-- A root in the paper's carrier forces `2l ∣ ord(q_v)`. -/
theorem paperOtriRoot_forces_twoL_dvd_order (r : paperOtri T b)
    (hr : (r : paperKv T b) ^ (2 * l.value) = (sectionQ T b).q) :
    2 * l.value ∣ (sectionQ T b).order :=
  two_l_dvd_order_of_root T b (r : paperKv T b) hr

/-- The same obstruction derived from the file's own order/coprimality data:
a root gives `l ∣ ord(q_v) = eSource * ord(q)`, and the F-side order is prime to
`l`, so `l ∣ eSource`.  This is the exact divisibility content of Example
3.2(iv) at the paper's place. -/
theorem paperOtriRoot_forces_l_dvd_of_coprime (r : paperOtri T b)
    (hr : (r : paperKv T b) ^ (2 * l.value) = (sectionQ T b).q) :
    l.value ∣ eSource T b := by
  have h2l : 2 * l.value ∣ (sectionQ T b).order :=
    paperOtriRoot_forces_twoL_dvd_order T b r hr
  have hl : l.value ∣ (sectionQ T b).order :=
    Nat.dvd_trans ⟨2, by ring⟩ h2l
  have her : l.value ∣ eSource T b * (shadowQ T b).order := by
    rw [← paperQV_order T b]
    exact hl
  exact (paperQ_shadowOrder_coprime T b).symm.dvd_of_dvd_mul_right her

/-! ## 7. The assembled paper attachment, and the no-fake no-gos -/

/-- The constructed paper `O^tri` attachment at the designated K-place: the
`O^⊿` carrier with the actual paper `q_v`, the actual `O^× → O^⊿` embedding and
the `O^×μ = μ_{2l}` subgroup.  The `2l`-th root `q_v^{1/2l}` is deliberately
*not* a field of this record: it is the missing datum `paperOtriRootMissing`. -/
structure PaperOtriAttachment where
  qv : paperOtri T b
  qv_eq_sectionQ : (qv : paperKv T b) = (sectionQ T b).q
  qv_norm_lt_one : ‖(qv : paperKv T b)‖ < 1
  unitsToOtri : paperOUnits T b →* paperOtri T b
  unitsToOtri_injective : Function.Injective unitsToOtri
  unitsMu_exponent : ∀ ζ : paperOUnitsMu T b, (ζ : paperOUnits T b) ^ (2 * l.value) = 1

/-- The paper attachment is constructed from the actual data above. -/
noncomputable def paperOtriAttachment : PaperOtriAttachment T b where
  qv := paperQV T b
  qv_eq_sectionQ := paperQV_val T b
  qv_norm_lt_one := paperQV_norm_lt_one T b
  unitsToOtri := paperOUnitsToOtri T b
  unitsToOtri_injective := paperOUnitsToOtri_injective T b
  unitsMu_exponent := paperOUnitsMu_pow T b

/-- The paper's `q_v` is the K-side base change, not the F-side `qVFamily`:
the F-side parameter has order prime to `l` and no completion `2l`-th root
(S342). -/
theorem no_Fside_completionRoot :
    ¬ Nonempty (TwoLthRootData (T := T) (b := b)) :=
  twoLthRootData_impossible T b

/-- **No fake completion-valued attachment of the F-side `qVFamily`.**  No monoid
evaluation into the F-side completion units can send a q-section with a root
section to the F-side `qVUnit` (S342; the same obstruction as S2057's and S681's
no-gos).  Hence the paper `q_v` cannot be the F-side repo `qVFamily`, and the
S346/`S357` bare-function carrier spec is not the faithful attachment. -/
theorem no_completionMonoidEval_of_Fside_qVFamily
    {M : Type u} [Monoid M] (qSection rootSection : M)
    (hroot : rootSection ^ (2 * l.value) = qSection)
    (φ : M →* (Completion ((nativeBadLift T).lift b))ˣ)
    (hq : φ qSection = qVUnit T b) : False := by
  refine twoLthRootData_impossible T b ⟨?_⟩
  refine { root := φ rootSection, root_pow := ?_ }
  show (φ rootSection) ^ (2 * l.value) = qVUnit T b
  rw [← map_pow, hroot, hq]

/-! ## 8. Axiom audit (in-file, so that one run is the verification) -/

#print axioms paperQV_norm_lt_one
#print axioms paperQV_eq_completionMap
#print axioms paperOUnitsToOtri_injective
#print axioms paperRootRatio_mem_mu
#print axioms paperClosureRoot_pow
#print axioms paperClosureRoot_ratio_pow_one
#print axioms paperOtriRootMissing_iff
#print axioms paperOtriRootInCompletion_iff_paperQV
#print axioms paperOtriRoot_forces_l_dvd_ramification
#print axioms paperOtriRoot_forces_l_dvd_of_coprime
#print axioms paperOtriAttachment
#print axioms no_Fside_completionRoot
#print axioms no_completionMonoidEval_of_Fside_qVFamily

end LeanFormal.IUT.XiFPaper.S2092PaperOtriActual
end
