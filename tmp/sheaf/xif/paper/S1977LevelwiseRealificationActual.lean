/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import tmp.sheaf.xif.paper.S1961LocalGlobalBridgeActual

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# S1977: the levelwise realification functional of the actual p-adic log-shell

Layer: **O** (original Theta-link / q-pilot), consumer of S1961, S1949, S1927.

## The question

S1961 proved the IQ (Q-span) level local-global bridge

  bridgeFiber v = Submodule.span Q (realBridge v '' actualLogShell_v),
  bridgePacket = paperGlobalLogShellPacket,

where realBridge v x = Real.log ‖x‖ is the norm-log readout on the actual
p-adic completion K_v = Completion (QPlace v).  The levelwise equality

  realBridge v '' actualLogShell_v = (paperLogShellDatum v).logShell

is *not* proved by S1961 (and is false).  The remaining object named there is
"an additive real-valued functional on Completion (QPlace v) compatible with
the norm-log readout".  This file attacks exactly that object.

## What this file proves

1. **The levelwise norm-log functional that exists.**  The additive real-valued
   functional compatible with the norm-log readout lives on the *multiplicative*
   group of the completion, written additively:

     additiveNormLog v : Additive (Completion (QPlace v))ˣ →+ ℝ,
     u ↦ Real.log ‖u‖,

   and on the monoid side as the norm-log degree
   levelwiseNormLog v : (Completion (QPlace v))ˣ →* Multiplicative ℝ.
   It identifies the reduced S1927 shell **levelwise**:

     paperPreLogShell v = range (u ↦ additiveNormLog v u),
     paperLogShell v = (fun a => (p*_v)⁻¹ * a) '' range (u ↦ additiveNormLog v u).

   These are identities of sets, not of spans.

2. **The actual datum's units carry no norm-log information.**
   Every unit of the completed integer ring O_v has norm 1
   (completionUnits_norm_eq_one), hence

     realBridge v '' (coercion of (O_v)ˣ) = {0}.

   So the norm-log readout of the actual unit group (the Units field of
   actualLocalLogShellDatum) is trivial, while the reduced datum's Units is the
   full multiplicative group K_vˣ, whose norm-log image is the nonzero lattice
   of Real.log ‖x‖.

3. **No additive real-valued functional on the additive group of the
   completion agrees with the norm-log bridge on the actual log-shell**
   (no_additive_realification).  The actual log-shell is an additive subgroup
   containing 0 and, for a chosen uniformizer pi, the elements
   pi, pi + pi, (pi+pi) + (pi+pi).  Additivity would force

     log ‖2‖ = log ‖pi‖  (from pi + pi)  and  log ‖2‖ = log ‖2 pi‖
     (from (pi+pi) + (pi+pi)), while multiplicativity of the norm gives
     log ‖2 pi‖ = log ‖2‖ + log ‖pi‖; hence log ‖pi‖ = 0, contradicting
     ‖pi‖ < 1.  This is a genuine obstruction, not a missing lemma: the
     proposed functional is provably absent.

4. **The proposed object is an empty structure.**
   LevelwiseRealificationFunctional v records an additive
   Completion (QPlace v) →+ ℝ that agrees with the norm-log bridge on the
   actual log-shell and maps it levelwise onto the reduced S1927 shell;
   levelwiseRealificationFunctional_not_nonempty proves that no such object
   exists (already the two compatibility fields are inconsistent).

5. **The levelwise set equality is false for *every* function.**
   levelwise_equality_false shows realBridgeImage v ≠ paperLogShell v; the
   bridge image is bounded above (the actual log-shell is compact, hence
   bounded, and the norm-log readout of a bounded nonzero element is bounded
   above), while the reduced shell is unbounded above
   (paperLogShell_unbounded).  Consequently no function whatsoever, additive or
   not, can be the norm-log readout on the actual log-shell and hit the reduced
   shell (no_levelwise_realification_function).

6. **The units-side variant of the compatibility is degenerate.**
   If one instead demands L (log u) = log ‖u‖ for actual integral units u, then
   L vanishes on the whole pre-log-shell
   (additive_functional_trivial_on_preLogShell), because every integral unit has
   norm 1; the reduced shell is not {0}, so this variant cannot produce the
   levelwise comparison either.

7. **The sharp true statement.**  The Q-span identity of S1961
   (s1977_span_bridge_sharp) is exactly the level of the bridge at which the
   two different unit groups O_vˣ and K_vˣ are reconciled.

## Exact first missing (the precise replacement of the proposed functional)

The remaining object is **not** an additive real-valued functional on
Completion (QPlace v), and it is not a missing lemma either: the levelwise
comparison of the actual p-adic log-shell with the reduced real log-shell is
false at the level of sets, and every additive functional agreeing with the
norm-log readout on the actual shell is inconsistent.  Precisely, the missing
datum is an identification

  O_vˣ  ~  K_vˣ

of the actual integral unit group with the completion's full multiplicative
group **compatible with the norm-log readout**, i.e. a uniformizer-splitting
under which the norm-log of an integral unit (identically 0) is compared with
the norm-log of a field unit (the lattice Z * log ‖pi‖).  Such an
identification cannot be compatible with the norm-log readout because the left
readout is trivial (realBridge_image_completionUnits).  What survives is exactly
the Q-span comparison of S1961, and the correct levelwise realification lives
on the multiplicative group, where it is constructed here (additiveNormLog,
items 1-2 above).

## Honest scope

No sorry, admit, axiom, True/PUnit slot, empty type, arbitrary inhabitant or
Nonempty gate is used.  The impossibility statements are theorems about the
actual S1949/S1927 objects; nothing is postulated.  Axiom probes are at the end
of the file.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S1977LevelwiseRealificationActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.XiFPaper.S1927GlobalFrobenioidLogShellActual
open LeanFormal.IUT.XiFPaper.S1949NonarchimedeanLogShellActual
open LeanFormal.IUT.XiFPaper.S1961LocalGlobalBridgeActual
open LeanFormal.IUT.XiFPaper.OneColumnFinitePrimePlaceActual
open LeanFormal.IUT.NumberFieldFinitePlace

/-! ## 0. The reduced S1927 shells as sets of reals -/

/-- The reduced S1927 local pre-log-shell, with the real codomain made explicit. -/
def paperPreLogShell (v : FinitePrimePlace 2 7) : Set ℝ :=
  ((paperLogShellDatum v).preLogShell : Set ℝ)

/-- The reduced S1927 local log-shell, with the real codomain made explicit. -/
def paperLogShell (v : FinitePrimePlace 2 7) : Set ℝ :=
  ((paperLogShellDatum v).logShell : Set ℝ)

/-- The explicit real form is the S1927 reduced pre-log-shell. -/
theorem paperPreLogShell_eq_datum (v : FinitePrimePlace 2 7) :
    paperPreLogShell v = (paperLogShellDatum v).preLogShell := rfl

/-- The explicit real form is the S1927 reduced log-shell. -/
theorem paperLogShell_eq_datum (v : FinitePrimePlace 2 7) :
    paperLogShell v = (paperLogShellDatum v).logShell := rfl

/-- Membership in the reduced log-shell is the (p*_v)-scaling law, read in ℝ. -/
theorem mem_paperLogShell_iff (v : FinitePrimePlace 2 7) {x : ℝ} :
    x ∈ paperLogShell v ↔
      ((paperLogShellDatum v).pStar : ℝ) * x ∈ paperPreLogShell v := by
  unfold paperLogShell paperPreLogShell
  exact Iff.rfl

/-- The reduced p*_v factor is a positive real number. -/
theorem paperPStar_pos (v : FinitePrimePlace 2 7) :
    (0:ℝ) < ((paperLogShellDatum v).pStar : ℝ) := by
  exact_mod_cast (paperLogShellDatum v).pStar_pos

/-- The reduced p*_v factor is a nonzero real number. -/
theorem paperPStar_ne_zero (v : FinitePrimePlace 2 7) :
    ((paperLogShellDatum v).pStar : ℝ) ≠ 0 :=
  (paperPStar_pos v).ne'

/-! ## 1. The levelwise norm-log realification functional

The additive real-valued functional compatible with the norm-log readout exists
on the multiplicative group of the actual completion.  It is the additive form
of the norm-log degree Real.log ‖-‖. -/

/-- The levelwise norm-log functional: the norm-log degree as a monoid
homomorphism from the multiplicative group of the actual completion to the
additive real line. -/
noncomputable def levelwiseNormLog (v : FinitePrimePlace 2 7) :
    (Completion (QPlace v))ˣ →* Multiplicative ℝ :=
  unitNormLogDegree (Completion (QPlace v))

/-- Levelwise, the norm-log functional reads out exactly the S1961 bridge
realBridge v x = log ‖x‖ on every unit of the completion. -/
@[simp] theorem levelwiseNormLog_apply (v : FinitePrimePlace 2 7)
    (u : (Completion (QPlace v))ˣ) :
    (levelwiseNormLog v u).toAdd = realBridge v (u : Completion (QPlace v)) := rfl

/-- **The additive real-valued functional compatible with the norm-log readout**,
on the multiplicative group of the completion written additively.  This is the
honest home of the levelwise realification: the domain is the multiplicative
group K_vˣ, not the additive group of K_v. -/
noncomputable def additiveNormLog (v : FinitePrimePlace 2 7) :
    Additive ((Completion (QPlace v))ˣ) →+ ℝ where
  toFun u := Real.log ‖((Additive.toMul u : (Completion (QPlace v))ˣ) :
    Completion (QPlace v))‖
  map_zero' := by
    show Real.log ‖((1 : (Completion (QPlace v))ˣ) : Completion (QPlace v))‖ = 0
    rw [Units.val_one, norm_one, Real.log_one]
  map_add' u w := by
    have hval : Additive.toMul (u + w) =
        Additive.toMul u * Additive.toMul w := rfl
    show Real.log ‖((Additive.toMul (u + w) : (Completion (QPlace v))ˣ) :
        Completion (QPlace v))‖ =
      Real.log ‖((Additive.toMul u : (Completion (QPlace v))ˣ) :
        Completion (QPlace v))‖ +
      Real.log ‖((Additive.toMul w : (Completion (QPlace v))ˣ) :
        Completion (QPlace v))‖
    rw [hval, Units.val_mul, norm_mul,
      Real.log_mul (norm_ne_zero_iff.mpr (Units.ne_zero _))
        (norm_ne_zero_iff.mpr (Units.ne_zero _))]

/-- The additive functional reads out the norm-log bridge on every unit. -/
@[simp] theorem additiveNormLog_ofMul (v : FinitePrimePlace 2 7)
    (u : (Completion (QPlace v))ˣ) :
    additiveNormLog v (Additive.ofMul u) =
      realBridge v (u : Completion (QPlace v)) := rfl

/-- **Levelwise identity for the reduced pre-log-shell**: the reduced S1927
pre-log-shell is exactly the image of the additive norm-log functional on the
multiplicative group of the actual completion. -/
theorem paperPreLogShell_eq_levelwiseNormLog_range (v : FinitePrimePlace 2 7) :
    paperPreLogShell v =
      Set.range (fun u : (Completion (QPlace v))ˣ => (levelwiseNormLog v u).toAdd) := by
  ext a
  unfold paperPreLogShell
  constructor
  · rintro ⟨u, -, h⟩
    exact ⟨u, h⟩
  · rintro ⟨u, h⟩
    exact ⟨u, trivial, h⟩

/-- **Levelwise identity for the reduced log-shell**: the reduced S1927
log-shell is exactly the (p*_v)⁻¹-scaled norm-log image of the multiplicative
group of the actual completion.  This is a set identity, not a span identity. -/
theorem paperLogShell_eq_levelwiseNormLog_image (v : FinitePrimePlace 2 7) :
    paperLogShell v =
      (fun a : ℝ => ((paperLogShellDatum v).pStar : ℝ)⁻¹ * a) ''
        Set.range (fun u : (Completion (QPlace v))ˣ => (levelwiseNormLog v u).toAdd) := by
  ext b
  rw [mem_paperLogShell_iff, paperPreLogShell_eq_levelwiseNormLog_range]
  simp only [Set.mem_range, Set.mem_image]
  have hp : ((paperLogShellDatum v).pStar : ℝ) ≠ 0 := paperPStar_ne_zero v
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨(levelwiseNormLog v u).toAdd, ⟨u, rfl⟩, ?_⟩
    rw [hu]
    field_simp
  · rintro ⟨x, ⟨u, hu⟩, hx⟩
    refine ⟨u, ?_⟩
    rw [hu]
    rw [← hx]
    field_simp

/-! ## 2. The actual unit group carries trivial norm-log information -/

/-- Units of the actual completed integer ring have norm one: the unit and its
inverse both lie in the valuation ring, so both norms are at most 1 while their
product is 1. -/
theorem completionUnits_norm_eq_one (v : FinitePrimePlace 2 7)
    (u : (CompletionIntegers (QPlace v))ˣ) :
    ‖((u : CompletionIntegers (QPlace v)) : Completion (QPlace v))‖ = 1 := by
  have hu : ‖((u : CompletionIntegers (QPlace v)) : Completion (QPlace v))‖ ≤ 1 :=
    (mem_completionIntegers_iff_norm_le_one (QPlace v) _).mp
      (u : CompletionIntegers (QPlace v)).property
  have hu' : ‖(((u⁻¹ : (CompletionIntegers (QPlace v))ˣ) :
      CompletionIntegers (QPlace v)) : Completion (QPlace v))‖ ≤ 1 :=
    (mem_completionIntegers_iff_norm_le_one (QPlace v) _).mp
      ((u⁻¹ : (CompletionIntegers (QPlace v))ˣ) : CompletionIntegers (QPlace v)).property
  have hcongr : (((u * u⁻¹ : (CompletionIntegers (QPlace v))ˣ) :
      CompletionIntegers (QPlace v)) : Completion (QPlace v)) = 1 := by
    rw [mul_inv_cancel]
    rfl
  have hmul : ((u : CompletionIntegers (QPlace v)) : Completion (QPlace v)) *
      (((u⁻¹ : (CompletionIntegers (QPlace v))ˣ) :
        CompletionIntegers (QPlace v)) : Completion (QPlace v)) = 1 := by
    rw [← hcongr]
    rfl
  have hprod : ‖((u : CompletionIntegers (QPlace v)) : Completion (QPlace v))‖ *
      ‖(((u⁻¹ : (CompletionIntegers (QPlace v))ˣ) :
        CompletionIntegers (QPlace v)) : Completion (QPlace v))‖ = 1 := by
    rw [← norm_mul, hmul, norm_one]
  have h1 : (0:ℝ) ≤ ‖((u : CompletionIntegers (QPlace v)) : Completion (QPlace v))‖ :=
    norm_nonneg _
  have h2 : (0:ℝ) ≤ ‖(((u⁻¹ : (CompletionIntegers (QPlace v))ˣ) :
      CompletionIntegers (QPlace v)) : Completion (QPlace v))‖ := norm_nonneg _
  have hge : 1 ≤ ‖((u : CompletionIntegers (QPlace v)) : Completion (QPlace v))‖ := by
    nlinarith
  exact le_antisymm hu hge

/-- The norm-log bridge vanishes on the actual unit group. -/
theorem realBridge_completionUnits_eq_zero (v : FinitePrimePlace 2 7)
    (u : (CompletionIntegers (QPlace v))ˣ) :
    realBridge v ((u : CompletionIntegers (QPlace v)) : Completion (QPlace v)) = 0 := by
  show Real.log ‖((u : CompletionIntegers (QPlace v)) : Completion (QPlace v))‖ = 0
  rw [completionUnits_norm_eq_one v u, Real.log_one]

/-- **The actual datum's unit group has trivial norm-log readout**: the bridge
image of the set of O_vˣ-elements is the singleton {0}, whereas the reduced
datum's unit group K_vˣ has the nonzero norm-log image of Section 1. -/
theorem realBridge_image_completionUnits (v : FinitePrimePlace 2 7) :
    realBridge v '' Set.range (fun u : (CompletionIntegers (QPlace v))ˣ =>
      ((u : CompletionIntegers (QPlace v)) : Completion (QPlace v))) = {0} := by
  ext y
  constructor
  · rintro ⟨x, ⟨u, rfl⟩, rfl⟩
    exact realBridge_completionUnits_eq_zero v u
  · rintro rfl
    exact ⟨((1 : (CompletionIntegers (QPlace v))ˣ) : Completion (QPlace v)),
      ⟨1, rfl⟩, by simp [realBridge]⟩

/-! ## 3. The levelwise equality is false -/

/-- A positive norm bound for the actual log-shell: the shell is compact, hence
bounded in the normed completion, and 0 lies in it. -/
theorem completionLogShell_norm_bound (v : FinitePrimePlace 2 7) :
    ∃ C : ℝ, 0 < C ∧
      ∀ x ∈ (completionLogShell (QPlace v) : Set (Completion (QPlace v))), ‖x‖ ≤ C := by
  have hb : Bornology.IsBounded
      ((completionLogShell (QPlace v) : Set (Completion (QPlace v)))) :=
    (isCompact_completionLogShell (QPlace v)).isBounded
  rw [Metric.isBounded_iff] at hb
  obtain ⟨r, hr⟩ := hb
  have hzero : (0 : Completion (QPlace v)) ∈
      (completionLogShell (QPlace v) : Set (Completion (QPlace v))) :=
    (completionLogShell (QPlace v)).zero_mem
  refine ⟨max r 1, by positivity, ?_⟩
  intro x hx
  have h1 : dist x 0 ≤ r := hr hx hzero
  rw [dist_zero_right] at h1
  exact le_trans h1 (le_max_left _ _)

/-- The actual log-shell is norm bounded. -/
theorem actualLogShell_norm_bound (v : FinitePrimePlace 2 7) :
    ∃ C : ℝ, 0 < C ∧
      ∀ x : Completion (QPlace v),
        x ∈ (actualLocalLogShellDatum v).logShell → ‖x‖ ≤ C := by
  obtain ⟨C, hCpos, hC⟩ := completionLogShell_norm_bound v
  refine ⟨C, hCpos, ?_⟩
  intro x hx
  exact hC x (by rwa [actualLogShell_eq_completionLogShell v] at hx)

/-- The norm-log bridge image of the actual log-shell is bounded above: the
logarithm of a norm bounded by C > 0 is at most Real.log C, and x = 0 reads out
0. -/
theorem realBridgeImage_boundedAbove (v : FinitePrimePlace 2 7) :
    ∃ U : ℝ, ∀ y ∈ realBridgeImage v, y ≤ U := by
  obtain ⟨C, hCpos, hC⟩ := actualLogShell_norm_bound v
  refine ⟨max 0 (Real.log C), ?_⟩
  rintro y ⟨x, hx, rfl⟩
  by_cases hx0 : x = 0
  · subst hx0
    simp [realBridge]
  · have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hle : Real.log ‖x‖ ≤ Real.log C := Real.log_le_log hpos (hC x hx)
    exact le_trans hle (le_max_right _ _)

/-- **The reduced S1927 log-shell is unbounded above.**  The norm-log of the
inverse of a field uniformizer pi is positive, and the reduced shell contains
the (p*_v)⁻¹-scaled additive multiples of that positive number, which are
unbounded. -/
theorem paperLogShell_unbounded (v : FinitePrimePlace 2 7) :
    ∀ U : ℝ, ∃ a ∈ paperLogShell v, U < a := by
  intro U
  set p : ℝ := ((paperLogShellDatum v).pStar : ℝ) with hp_def
  have hp : 0 < p := paperPStar_pos v
  set b : ℝ := Real.log ‖((actualUniformizer v : Completion (QPlace v)))⁻¹‖ with hb_def
  have hpi_ne : (actualUniformizer v : Completion (QPlace v)) ≠ 0 :=
    actualUniformizer_coe_ne_zero v
  have hpi_pos : 0 < ‖(actualUniformizer v : Completion (QPlace v))‖ :=
    norm_pos_iff.mpr hpi_ne
  have hpi_lt : ‖(actualUniformizer v : Completion (QPlace v))‖ < 1 :=
    actualUniformizer_norm_lt_one v
  have hbpos : 0 < b := by
    rw [hb_def, norm_inv, Real.log_inv]
    have hneg : Real.log ‖(actualUniformizer v : Completion (QPlace v))‖ < 0 := by
      have hlt := Real.log_lt_log hpi_pos hpi_lt
      rwa [Real.log_one] at hlt
    linarith
  have hbmem : b ∈ paperPreLogShell v := by
    rw [paperPreLogShell_eq_levelwiseNormLog_range]
    refine ⟨Units.mk0 (((actualUniformizer v : Completion (QPlace v)))⁻¹)
      (inv_ne_zero hpi_ne), ?_⟩
    rw [hb_def]
    rfl
  have hcpos : 0 < p⁻¹ * b := mul_pos (inv_pos.mpr hp) hbpos
  have hcmem : p⁻¹ * b ∈ paperLogShell v := by
    rw [mem_paperLogShell_iff, ← hp_def, ← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul]
    exact hbmem
  have hpow : ∀ n : ℕ, (n:ℝ) * (p⁻¹ * b) ∈ paperLogShell v := by
    intro n
    induction n with
    | zero =>
        have h0 : (0:ℝ) ∈ paperPreLogShell v := by
          rw [paperPreLogShell_eq_levelwiseNormLog_range]
          exact ⟨1, by simp⟩
        have hz : (0:ℝ) ∈ paperLogShell v := by
          rw [mem_paperLogShell_iff]
          simpa using h0
        simpa [zero_mul] using hz
    | succ k ih =>
        have hstep : ((k:ℝ) + 1) * (p⁻¹ * b) = (k:ℝ) * (p⁻¹ * b) + (p⁻¹ * b) := by
          ring
        have hcast : ((k + 1 : ℕ) : ℝ) = (k:ℝ) + 1 := by push_cast; ring
        rw [hcast, hstep]
        exact SourceLogShellDatum.add_mem_logShell (paperLogShellDatum v) ih hcmem
  obtain ⟨n, hn⟩ : ∃ n : ℕ, U / (p⁻¹ * b) < n := exists_nat_gt _
  refine ⟨(n:ℝ) * (p⁻¹ * b), hpow n, ?_⟩
  rw [div_lt_iff₀ hcpos] at hn
  linarith

/-- **The levelwise equality of S1961's bridge with the reduced shell is
false**: the bridge image is bounded above, while the reduced shell is unbounded
above. -/
theorem levelwise_equality_false (v : FinitePrimePlace 2 7) :
    realBridgeImage v ≠ paperLogShell v := by
  intro hEq
  obtain ⟨U, hU⟩ := realBridgeImage_boundedAbove v
  obtain ⟨a, ha, hgt⟩ := paperLogShell_unbounded v U
  have hUa : a ≤ U := by
    rw [← hEq] at ha
    exact hU a ha
  linarith

/-- The same inequality in the exact form of S1961's reduced datum. -/
theorem levelwise_equality_false_datum (v : FinitePrimePlace 2 7) :
    realBridgeImage v ≠ ((paperLogShellDatum v).logShell : Set ℝ) :=
  levelwise_equality_false v

/-- The bridge image consists of integer multiples of the norm-log generator
L_v = Real.log (absNorm maximalIdeal). -/
theorem realBridgeImage_subset_intMultiples (v : FinitePrimePlace 2 7) :
    ∀ y ∈ realBridgeImage v, ∃ k : ℤ, y = (k : ℝ) * absNormLog v := by
  rintro y ⟨x, -, rfl⟩
  by_cases hx0 : x = 0
  · subst hx0
    exact ⟨0, by simp [realBridge]⟩
  · refine ⟨Multiplicative.toAdd (WithZero.unzero
      (valuation_ne_zero_of_ne_zero (QPlace v) x hx0)), ?_⟩
    show Real.log ‖x‖ = _
    rw [logNorm_eq_absNorm_mul (QPlace v) x hx0, absNormLog]

/-! ## 4. The additive norm-log-compatible functional on the additive group of
the completion does not exist -/

/-- **Main obstruction: no additive real-valued functional on the additive group
of the actual p-adic completion agrees with the norm-log bridge on the actual
log-shell.**

The log-shell is an additive subgroup containing a uniformizer pi and its
integer multiples.  Additivity applied to pi + pi and to (pi+pi) + (pi+pi)
forces log ‖pi‖ = 0, contradicting ‖pi‖ < 1.  No sorry, no missing lemma: the
object is inconsistent. -/
theorem no_additive_realification (v : FinitePrimePlace 2 7) :
    ¬ ∃ L : Completion (QPlace v) →+ ℝ,
        ∀ x ∈ (actualLocalLogShellDatum v).logShell, L x = realBridge v x := by
  rintro ⟨L, hL⟩
  set a : Completion (QPlace v) := (actualUniformizer v : Completion (QPlace v)) with ha
  have ha0 : a ≠ 0 := by
    rw [ha]
    exact actualUniformizer_coe_ne_zero v
  have hamem : a ∈ (actualLocalLogShellDatum v).logShell := by
    rw [ha]
    exact actualUniformizer_logNorm_mem_actualLogShell v
  have h2mem : a + a ∈ (actualLocalLogShellDatum v).logShell :=
    SourceLogShellDatum.add_mem_logShell (actualLocalLogShellDatum v) hamem hamem
  have h4mem : (a + a) + (a + a) ∈ (actualLocalLogShellDatum v).logShell :=
    SourceLogShellDatum.add_mem_logShell (actualLocalLogShellDatum v) h2mem h2mem
  have ha2ne : a + a ≠ 0 := by
    have h : a + a = (2 : Completion (QPlace v)) * a := (two_mul a).symm
    rw [h]
    exact mul_ne_zero two_ne_zero ha0
  have hnorm2 : ‖(2 : Completion (QPlace v))‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    exact two_ne_zero
  have hnorma : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha0
  have hnorms2 : ‖a + a‖ ≠ 0 := norm_ne_zero_iff.mpr ha2ne
  have e1 : Real.log ‖a + a‖ =
      Real.log ‖(2 : Completion (QPlace v))‖ + Real.log ‖a‖ := by
    have h : a + a = (2 : Completion (QPlace v)) * a := (two_mul a).symm
    rw [h, norm_mul, Real.log_mul hnorm2 hnorma]
  have e2 : Real.log ‖a + a‖ = 2 * Real.log ‖a‖ := by
    have h1 : L (a + a) = L a + L a := map_add L a a
    have h2 : L (a + a) = Real.log ‖a + a‖ := by
      simpa [realBridge] using hL (a + a) h2mem
    have h3 : L a = Real.log ‖a‖ := by
      simpa [realBridge] using hL a hamem
    rw [h2, h3] at h1
    linarith
  have e3 : Real.log ‖(2 : Completion (QPlace v))‖ = Real.log ‖a‖ := by linarith
  have e4 : Real.log ‖(a + a) + (a + a)‖ =
      Real.log ‖(2 : Completion (QPlace v))‖ + Real.log ‖a + a‖ := by
    have h : (a + a) + (a + a) = (2 : Completion (QPlace v)) * (a + a) :=
      (two_mul (a + a)).symm
    rw [h, norm_mul, Real.log_mul hnorm2 hnorms2]
  have e5 : Real.log ‖(a + a) + (a + a)‖ = 2 * Real.log ‖a + a‖ := by
    have h1 : L ((a + a) + (a + a)) = L (a + a) + L (a + a) :=
      map_add L (a + a) (a + a)
    have h2 : L ((a + a) + (a + a)) = Real.log ‖(a + a) + (a + a)‖ := by
      simpa [realBridge] using hL ((a + a) + (a + a)) h4mem
    have h3 : L (a + a) = Real.log ‖a + a‖ := by
      simpa [realBridge] using hL (a + a) h2mem
    rw [h2, h3] at h1
    linarith
  have e6 : Real.log ‖(2 : Completion (QPlace v))‖ = Real.log ‖a + a‖ := by linarith
  have hzero : Real.log ‖a‖ = 0 := by linarith
  exact actualUniformizer_logNorm_ne_zero v (by rw [← ha]; exact hzero)

/-- The proposed levelwise realification functional: an additive real-valued
functional on the actual p-adic completion which agrees with the norm-log
bridge on the actual log-shell and whose levelwise image is the reduced S1927
log-shell. -/
structure LevelwiseRealificationFunctional (v : FinitePrimePlace 2 7) where
  /-- the additive real-valued functional -/
  toFun : Completion (QPlace v) →+ ℝ
  /-- it is compatible with the norm-log readout on the actual log-shell -/
  agrees_on_logShell : ∀ x ∈ (actualLocalLogShellDatum v).logShell,
    toFun x = realBridge v x
  /-- it realifies the actual log-shell levelwise onto the reduced shell -/
  image_logShell : toFun '' (actualLocalLogShellDatum v).logShell =
    paperLogShell v

/-- **The proposed object is empty**: already the additive plus
norm-log-compatibility fields are inconsistent. -/
theorem levelwiseRealificationFunctional_not_nonempty (v : FinitePrimePlace 2 7) :
    ¬ Nonempty (LevelwiseRealificationFunctional v) := by
  rintro ⟨F⟩
  exact no_additive_realification v ⟨F.toFun, F.agrees_on_logShell⟩

/-- **Even without additivity no levelwise realification exists**: the levelwise
set equality with the reduced shell fails for every function that reads out the
norm-log bridge on the actual log-shell.  The obstruction is set-theoretic (a
bounded image against an unbounded target), not merely the missing additive
structure. -/
theorem no_levelwise_realification_function (v : FinitePrimePlace 2 7) :
    ¬ ∃ f : Completion (QPlace v) → ℝ,
        (∀ x ∈ (actualLocalLogShellDatum v).logShell, f x = realBridge v x) ∧
        f '' (actualLocalLogShellDatum v).logShell = paperLogShell v := by
  rintro ⟨f, hf, himg⟩
  apply levelwise_equality_false v
  rw [← himg]
  unfold realBridgeImage
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, hf x hx⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, (hf x hx).symm⟩

/-- **The units-side compatibility is degenerate**: any additive functional whose
norm-log readout on the actual integral units is L (log u) = log ‖u‖ vanishes
on the whole pre-log-shell, because integral units have norm one. -/
theorem additive_functional_trivial_on_preLogShell (v : FinitePrimePlace 2 7)
    (L : Completion (QPlace v) →+ ℝ)
    (hL : ∀ u : (CompletionIntegers (QPlace v))ˣ,
      L (completionUnitLog (QPlace v) u) =
        Real.log ‖((u : CompletionIntegers (QPlace v)) : Completion (QPlace v))‖) :
    ∀ x ∈ (actualLocalLogShellDatum v).preLogShell, L x = 0 := by
  intro x hx
  rw [actualPreLogShell_eq_range] at hx
  obtain ⟨u, rfl⟩ := hx
  rw [hL u, completionUnits_norm_eq_one v u, Real.log_one]

/-! ## 5. The sharp true statement: the Q-span bridge of S1961 -/

/-- The Q-span identity of S1961 is the sharp level at which the actual p-adic
log-shell and the reduced real log-shell coincide; it is exactly the statement
that survives the levelwise obstruction above. -/
theorem s1977_span_bridge_sharp (v : FinitePrimePlace 2 7) :
    Submodule.span ℚ (realBridgeImage v) =
      Submodule.span ℚ (((paperLogShellDatum v).logShell) : Set ℝ) :=
  bridgeFiber_eq_paperSpan v

/-- The two local fibers of S1961, in the form used above. -/
theorem s1977_bridgeFiber_eq_span (v : FinitePrimePlace 2 7) :
    bridgeFiber v = Submodule.span ℚ (realBridgeImage v) := rfl

/-! ## 6. Axiom probes -/

#print axioms levelwiseNormLog_apply
#print axioms additiveNormLog_ofMul
#print axioms paperPreLogShell_eq_levelwiseNormLog_range
#print axioms paperLogShell_eq_levelwiseNormLog_image
#print axioms completionUnits_norm_eq_one
#print axioms realBridge_image_completionUnits
#print axioms completionLogShell_norm_bound
#print axioms actualLogShell_norm_bound
#print axioms realBridgeImage_boundedAbove
#print axioms paperLogShell_unbounded
#print axioms realBridgeImage_subset_intMultiples
#print axioms levelwise_equality_false
#print axioms levelwise_equality_false_datum
#print axioms no_additive_realification
#print axioms levelwiseRealificationFunctional_not_nonempty
#print axioms no_levelwise_realification_function
#print axioms additive_functional_trivial_on_preLogShell
#print axioms s1977_span_bridge_sharp

end LeanFormal.IUT.XiFPaper.S1977LevelwiseRealificationActual
