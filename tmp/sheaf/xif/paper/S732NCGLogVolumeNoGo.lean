import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Order.IntermediateValue

/-!
# S732: no-go statements for the NCG/index/trace/regulator reading of the paper log-volume

Research no-go file for task H (noncommutative geometry route to IUT III
Corollary 3.12).  Paper anchors:

* IUT III, Proposition 3.9, (i): the packet-normalized log-volume is normalized
  so that the reference integral structure O has log-volume 0, and so that
  multiplying a region by e adds 1.
* IUT III, Remark 3.9.4, (i): the log-volume is log of the integral over an
  ample measure space; additive translates of a region (relative to an additive
  structure preserving the measure) have the same log-volume.
* IUT III, Remark 3.9.5, (i): the holomorphic hull of a relatively compact
  region is the smallest region of the form lambda * O, so its log-volume is
  log |lambda|.

The statements below record four exact obstructions to reading this functional
as an index, a trace (Dixmier or otherwise), or a regulator:

1. PaperLogVolume.logVol_hull / cor312_scaling_iff: the paper log-volume of
   a hull is literally the logarithm of a scaling parameter, so the Cor 3.12
   comparison is a comparison of two scalars.
2. no_additive_of_scaling_and_translation: the paper's scaling law and Haar
   (translation) invariance are incompatible with additivity on disjoint
   regions, so the paper log-volume is not a linear trace/index functional.
3. trace_functional_blind_to_roots: every functional invariant under
   n-th roots of unity (every magnitude/trace functional) is blind to the
   2l-th root data of the root-stack carrier.
4. no_locallyConstant_int_eq_neg_log: an integer-valued locally constant
   "index" cannot equal the logarithm of a log-volume.

No paper theorem is claimed here.  These are structural no-go statements; the
paper-faithful inequality remains an object-level obligation.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S732NCGLogVolumeNoGo

/-! ## 1. The hull formula and the scalar form of the Cor 3.12 comparison -/

/-- Axiomatic paper log-volume on a type of regions (the role of M(-), the
compact closures of nonempty open subsets of Proposition 3.9, (i)).  The map
scale t is multiplication by the scaling t and O is the reference integral
structure. -/
structure PaperLogVolume (Region : Type*) where
  /-- The log-volume functional. -/
  logVol : Region → Real
  /-- Multiplication of a region by the scaling t. -/
  scale : Real → Region → Region
  /-- The reference integral structure O of Proposition 3.9, (i). -/
  O : Region
  /-- Packet normalization: the reference integral structure has log-volume 0. -/
  logVol_O : logVol O = 0
  /-- Scaling law of Remark 3.9.4, (i): multiplicaton by e adds 1. -/
  logVol_scale : ∀ (t : Real), 0 < t → ∀ R : Region,
    logVol (scale t R) = logVol R + Real.log t

namespace PaperLogVolume

variable {Region : Type*} (P : PaperLogVolume Region)

/-- Remark 3.9.5, (i): the log-volume of the hull lambda * O is log lambda
under the paper normalization. -/
theorem logVol_hull (t : Real) (ht : 0 < t) :
    P.logVol (P.scale t P.O) = Real.log t := by
  rw [P.logVol_scale t ht, P.logVol_O, zero_add]

/-- The hull log-volumes are ordered as the scaling parameters are ordered. -/
theorem logVol_hull_mono {s t : Real} (hs : 0 < s) (hst : s ≤ t) :
    P.logVol (P.scale s P.O) ≤ P.logVol (P.scale t P.O) := by
  rw [P.logVol_hull s hs, P.logVol_hull t (lt_of_lt_of_le hs hst)]
  exact Real.log_le_log hs hst

end PaperLogVolume

/-- Corollary 3.12, written for the two hull scalings tq (q side) and tTh
(Theta side): the paper inequality -|log Theta| >= -|log q|, i.e.
log tq <= log tTh, is exactly the scalar comparison tq <= tTh. -/
theorem cor312_scaling_iff {tq tTh : Real} (hq : 0 < tq) (hTh : 0 < tTh) :
    Real.log tq ≤ Real.log tTh ↔ tq ≤ tTh :=
  Real.log_le_log_iff hq hTh

/-! ## 2. The paper scaling law is incompatible with trace additivity -/

/-- Image of (0,1] under multiplication by 2. -/
theorem image_two_Ioc_zero_one :
    (fun x : Real => 2 * x) '' Set.Ioc 0 1 = Set.Ioc (0 : Real) 2 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  · intro hy
    exact ⟨y / 2, ⟨by linarith [hy.1], by linarith [hy.2]⟩, by ring⟩

/-- Image of (0,1] under translation by 1. -/
theorem image_add_one_Ioc :
    (fun x : Real => 1 + x) '' Set.Ioc 0 1 = Set.Ioc (1 : Real) 2 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  · intro hy
    exact ⟨y - 1, ⟨by linarith [hy.1], by linarith [hy.2]⟩, by ring⟩

/-- (0,2] is the disjoint union of (0,1] and (1,2]. -/
theorem Ioc_zero_two_eq_union :
    Set.Ioc (0 : Real) 2 = Set.Ioc 0 1 ∪ Set.Ioc 1 2 := by
  ext y
  constructor
  · intro hy
    by_cases h : y ≤ 1
    · exact Or.inl ⟨hy.1, h⟩
    · exact Or.inr ⟨lt_of_not_ge h, hy.2⟩
  · rintro (hy | hy)
    · exact ⟨hy.1, by linarith [hy.2]⟩
    · exact ⟨by linarith [hy.1], hy.2⟩

/-- Image of (0,1/2] under multiplication by 2. -/
theorem image_two_Ioc_half :
    (fun x : Real => 2 * x) '' Set.Ioc 0 (1 / 2) = Set.Ioc (0 : Real) 1 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  · intro hy
    exact ⟨y / 2, ⟨by linarith [hy.1], by linarith [hy.2]⟩, by ring⟩

/-- Image of (0,1/2] under translation by 1/2. -/
theorem image_add_half_Ioc :
    (fun x : Real => 1 / 2 + x) '' Set.Ioc 0 (1 / 2) =
      Set.Ioc (1 / 2 : Real) 1 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  · intro hy
    exact ⟨y - 1 / 2, ⟨by linarith [hy.1], by linarith [hy.2]⟩, by ring⟩

/-- (0,1] is the disjoint union of (0,1/2] and (1/2,1]. -/
theorem Ioc_zero_one_eq_union_half :
    Set.Ioc (0 : Real) 1 = Set.Ioc 0 (1 / 2) ∪ Set.Ioc (1 / 2) 1 := by
  ext y
  constructor
  · intro hy
    by_cases h : y ≤ 1 / 2
    · exact Or.inl ⟨hy.1, h⟩
    · exact Or.inr ⟨lt_of_not_ge h, hy.2⟩
  · rintro (hy | hy)
    · exact ⟨hy.1, by linarith [hy.2]⟩
    · exact ⟨by linarith [hy.1], hy.2⟩

/-- **No additive functional satisfies the paper log-volume axioms.**

hadd is trace/index additivity on disjoint regions; hscale is the paper scaling
law of Remark 3.9.4, (i) (multiplying by e adds 1); htrans is the Haar
invariance of Remark 3.9.4, (i) under the additive structure preserving the
measure.  The three together are contradictory.  Hence the paper log-volume is
log of a Haar measure, not a linear trace/index functional. -/
theorem no_additive_of_scaling_and_translation
    (L : Set Real → Real)
    (hadd : ∀ S T : Set Real, Disjoint S T → L (S ∪ T) = L S + L T)
    (hscale : ∀ (t : Real), 0 < t → ∀ S : Set Real,
      L ((fun x => t * x) '' S) = L S + Real.log t)
    (htrans : ∀ (a : Real), ∀ S : Set Real,
      L ((fun x => a + x) '' S) = L S) :
    False := by
  have hdisjAB : Disjoint (Set.Ioc (0 : Real) 1) (Set.Ioc (1 : Real) 2) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact absurd hx'.1 (not_lt.mpr hx.2)
  have hdisjDE : Disjoint (Set.Ioc (0 : Real) (1 / 2)) (Set.Ioc (1 / 2 : Real) 1) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact absurd hx'.1 (not_lt.mpr hx.2)
  have h2 : L (Set.Ioc (0 : Real) 2) = L (Set.Ioc (0 : Real) 1) + Real.log 2 := by
    rw [← image_two_Ioc_zero_one]
    exact hscale 2 (by norm_num) (Set.Ioc (0 : Real) 1)
  have hs : L (Set.Ioc (0 : Real) 2) =
      L (Set.Ioc (0 : Real) 1) + L (Set.Ioc (1 : Real) 2) := by
    rw [Ioc_zero_two_eq_union]
    exact hadd (Set.Ioc (0 : Real) 1) (Set.Ioc (1 : Real) 2) hdisjAB
  have ht : L (Set.Ioc (1 : Real) 2) = L (Set.Ioc (0 : Real) 1) := by
    rw [← image_add_one_Ioc]
    exact htrans 1 (Set.Ioc (0 : Real) 1)
  have hc : L (Set.Ioc (0 : Real) 1) = Real.log 2 := by linarith
  have h2' : L (Set.Ioc (0 : Real) 1) =
      L (Set.Ioc (0 : Real) (1 / 2)) + Real.log 2 := by
    rw [← image_two_Ioc_half]
    exact hscale 2 (by norm_num) (Set.Ioc (0 : Real) (1 / 2))
  have hD0 : L (Set.Ioc (0 : Real) (1 / 2)) = 0 := by linarith
  have hs' : L (Set.Ioc (0 : Real) 1) =
      L (Set.Ioc (0 : Real) (1 / 2)) + L (Set.Ioc (1 / 2 : Real) 1) := by
    rw [Ioc_zero_one_eq_union_half]
    exact hadd (Set.Ioc (0 : Real) (1 / 2)) (Set.Ioc (1 / 2 : Real) 1) hdisjDE
  have ht' : L (Set.Ioc (1 / 2 : Real) 1) = L (Set.Ioc (0 : Real) (1 / 2)) := by
    rw [← image_add_half_Ioc]
    exact htrans (1 / 2) (Set.Ioc (0 : Real) (1 / 2))
  have hlog : Real.log 2 = 0 := by linarith
  have hpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

/-! ## 3. Root blindness of trace/magnitude functionals -/

/-- Every functional invariant under n-th roots of unity (in particular every
functional of the complex magnitude, such as a trace functional in an operator
realization) cannot distinguish the n-th roots of an element. -/
theorem trace_functional_blind_to_roots {f : Complex → Real} {n : Nat}
    (hf : ∀ (z x : Complex), z ^ n = 1 → f (z * x) = f x) :
    ∀ x y : Complex, x ≠ 0 → x ^ n = y ^ n → f x = f y := by
  intro x y hx hpow
  have hz : (y / x) ^ n = 1 := by
    rw [div_pow, ← hpow, div_self (pow_ne_zero n hx)]
  have hy : y / x * x = y := div_mul_cancel₀ y hx
  rw [← hy]
  exact (hf (y / x) x hz).symm

/-- Multiplication by an n-th root of unity does not change the complex
magnitude: the elementary blindness of the log-volume to 2l-th root data of the
root-stack carrier. -/
theorem norm_mul_of_pow_eq_one {z : Complex} {n : Nat} (hz : z ^ n = 1) (hn : n ≠ 0)
    (x : Complex) : ‖z * x‖ = ‖x‖ := by
  rw [norm_mul, Complex.norm_eq_one_of_pow_eq_one hz hn, one_mul]

/-! ## 4. No discrete index equals the log-volume -/

/-- An integer-valued locally constant "index" cannot equal the logarithm of a
log-volume: log 1 = 0 and log 2 ne 0 are not both attained by an integer index
that is locally constant on [1,2]. -/
theorem no_locallyConstant_int_eq_neg_log :
    ¬ ∃ f : Real → Int, IsLocallyConstant f ∧
      ∀ x : Real, 1 ≤ x → x ≤ 2 → (f x : Real) = - Real.log x := by
  rintro ⟨f, hf, hlog⟩
  have h12 : f 1 = f 2 :=
    hf.apply_eq_of_isPreconnected (s := Set.Icc (1 : Real) 2) isPreconnected_Icc
      (by norm_num) (by norm_num)
  have e1 : (f 1 : Real) = 0 := by
    have h := hlog 1 le_rfl (by norm_num)
    simpa using h
  have e2 : (f 2 : Real) = - Real.log 2 := hlog 2 (by norm_num) le_rfl
  have hzero : (0 : Real) = - Real.log 2 := by
    calc (0 : Real) = (f 1 : Real) := e1.symm
      _ = (f 2 : Real) := by rw [h12]
      _ = - Real.log 2 := e2
  have hpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

end LeanFormal.IUT.XiFPaper.S732NCGLogVolumeNoGo

end