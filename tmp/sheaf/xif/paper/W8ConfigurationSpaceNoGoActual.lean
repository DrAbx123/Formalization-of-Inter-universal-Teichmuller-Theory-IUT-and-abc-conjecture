import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Connected.PathConnected

/-! # W8: configuration space / persistent topology no-go

Task W8 proposed reading the qPilot-Theta compatibility of the paper-faithful
Cor 3.12 as a path/homotopy statement in a configuration space of possible
Theta images/hulls, with qPilot as basepoint and the dimension supplied by the
labels/intermediate objects.

This file records the exact obstructions that survive formalization on the
local factor.  It does not prove the paper target and does not change it.

## Positive side (already in the tree, not duplicated here)

* The least lambda-O hull is the fractional-lattice region at the paper
  coefficient order/(2l) (S793, S799, S801, S810); the exponent space is the
  convex set (qVFamTensorV -> Real) and the region map is order-reversing, so
  the least hull is the join of the image points.  This is order theory, and
  S793 proves it in two lines.
* The skeleton dictionary (S814) identifies the region with a segment
  [c, infinity) of the value-group skeleton and the normalized log with minus
  its length; the paper inequality is then a segment inclusion.  This is
  order + Haar measure, not homotopy.
* The finite root stack L(mu_{2l}) (S782) with the actual mu_{2l}-invariant
  Haar measure (S824) is the only place where a genuine transformation acts;
  it gives the unconditional 1/(2l) log-divisor identity, not the hull log.

## Negative side (this file)

1. No homeomorphism-invariant functional of the region can equal the
   normalized Haar log.  On Q_p the dilation x |-> p * x is a homeomorphism
   carrying the unit ball onto the ball of radius p^{-1}, while the normalized
   log changes by -log p != 0.  Hence every topological invariant
   (homeomorphism type, homotopy type, singular homology) is blind to the
   exponent.  The same argument applies to the paper carrier once the
   finite-dimensional Q_p-topology and the pure-tensor dilation are supplied;
   that transfer is not formalized here (the tensor block currently has no
   topological-space instance in the tree).

2. Paths degenerate in the p-adic carrier: Q_p is totally disconnected, so
   every path is constant and every path-connected subset is a subsingleton.
   "qPilot and Theta are path-connected" is therefore false as a statement
   about points of the carrier; as a statement about the exponent parameter
   space it is true but vacuous.

3. Path-connectedness is a symmetric relation; the paper comparison
   qPilotLog <= hullLog is directional.  A symmetric relation cannot imply a
   directional inequality (the abstract lemma below).  Explicitly, on the
   one-factor exponent space the two points 0 and 1 are path-connected, but
   the comparison fails in the direction that would be needed if the
   basepoint were assigned the smaller exponent.

No fake hull, no surrogate target, no new axiom. -/

noncomputable section
open Metric Set

namespace LeanFormal.IUT.XiFPaper.W8ConfigurationSpaceNoGoActual

/-! ## 1. The p-adic model: dilation, log, and topology -/

variable {p : ℕ} [Fact p.Prime]

/-- The closed ball of radius p^{-k} in Q_p. -/
def padicBall (k : ℤ) : Set ℚ_[p] := closedBall 0 ((p : ℝ) ^ (-k))

/-- The normalized log volume of the ball of radius p^{-k}. -/
def ballLog (k : ℤ) : ℝ := -(k : ℝ) * Real.log (p : ℝ)

theorem padicBall_zero : padicBall (p := p) 0 = closedBall (0 : ℚ_[p]) 1 := by
  simp [padicBall]

theorem padicBall_one : padicBall (p := p) 1 = closedBall (0 : ℚ_[p]) ((p : ℝ)⁻¹) := by
  simp [padicBall]

theorem p_ne_zero_padic : (p : ℚ_[p]) ≠ 0 := by
  exact_mod_cast (Fact.out : p.Prime).ne_zero

/-- The dilation x |-> p * x carries the unit ball onto the ball of radius
p^{-1}.  This is the local model of the pure-tensor dilation that shifts the
lambda-O exponent by 1 on the paper tensor block. -/
theorem image_unitBall :
    padicBall (p := p) 1 =
      (fun x : ℚ_[p] => (p : ℚ_[p]) * x) '' padicBall (p := p) 0 := by
  ext x
  constructor
  · intro hx
    refine ⟨(p : ℚ_[p])⁻¹ * x, ?_, ?_⟩
    · simp only [padicBall, mem_closedBall, dist_zero_right] at hx ⊢
      rw [norm_mul, norm_inv, Padic.norm_p, inv_inv]
      have hx' : ‖x‖ ≤ (p : ℝ)⁻¹ := by simpa using hx
      have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_le
      calc (p : ℝ) * ‖x‖ ≤ (p : ℝ) * (p : ℝ)⁻¹ := by
            exact mul_le_mul_of_nonneg_left hx' (by positivity)
        _ = 1 := by field_simp
    · change (p : ℚ_[p]) * ((p : ℚ_[p])⁻¹ * x) = x
      rw [← mul_assoc, mul_inv_cancel₀ p_ne_zero_padic, one_mul]
  · rintro ⟨y, hy, rfl⟩
    simp only [padicBall, mem_closedBall, dist_zero_right] at hy ⊢
    rw [norm_mul, Padic.norm_p]
    have hy' : ‖y‖ ≤ 1 := by simpa using hy
    calc (p : ℝ)⁻¹ * ‖y‖ ≤ (p : ℝ)⁻¹ * 1 := by
          exact mul_le_mul_of_nonneg_left hy' (by positivity)
      _ = (p : ℝ) ^ (-1 : ℤ) := by simp

/-- No topological log.  No functional of the region that is invariant under
ambient homeomorphisms can agree with the normalized Haar log on the balls of
Q_p. -/
theorem no_homeomorphism_invariant_padic_log
    (F : Set ℚ_[p] → ℝ)
    (hinv : ∀ (h : ℚ_[p] ≃ₜ ℚ_[p]) (S : Set ℚ_[p]), F (h '' S) = F S) :
    ¬ (∀ k : ℤ, F (padicBall (p := p) k) = ballLog (p := p) k) := by
  intro hF
  have himg : (Homeomorph.smulOfNeZero (p : ℚ_[p]) p_ne_zero_padic) ''
      padicBall (p := p) 0 = padicBall (p := p) 1 := by
    rw [show (Homeomorph.smulOfNeZero (p : ℚ_[p]) p_ne_zero_padic : ℚ_[p] → ℚ_[p]) =
        fun x => (p : ℚ_[p]) * x from rfl]
    exact (image_unitBall (p := p)).symm
  have heq : F (padicBall (p := p) 1) = F (padicBall (p := p) 0) := by
    rw [← himg]
    exact hinv _ _
  rw [hF 1, hF 0] at heq
  simp only [ballLog, Int.cast_zero, Int.cast_one, zero_mul, one_mul, neg_mul] at heq
  have hlog : Real.log (p : ℝ) = 0 := by linarith
  exact (Real.log_pos (by exact_mod_cast (Fact.out : p.Prime).one_lt)).ne' hlog

/-- Every path in Q_p is constant: Q_p is totally disconnected, and the image
of the preconnected interval is a singleton. -/
theorem padic_path_eq {x y : ℚ_[p]} (γ : Path x y) : x = y := by
  have hpre : IsPreconnected (range γ) := isPreconnected_range γ.continuous
  have hsub := hpre.subsingleton
  have hx : x ∈ range γ := ⟨0, γ.source⟩
  have hy : y ∈ range γ := ⟨1, γ.target⟩
  exact hsub hx hy

/-- No path-connected subset of Q_p contains two distinct points. -/
theorem padic_isPathConnected_subsingleton {s : Set ℚ_[p]}
    (hs : IsPathConnected s) : s.Subsingleton := by
  intro x hx y hy
  exact padic_path_eq (hs.joinedIn x hx y hy).somePath

/-- Q_p has no nontrivial path-connected subset. -/
theorem padic_no_nontrivial_pathConnected :
    ¬ ∃ s : Set ℚ_[p], IsPathConnected s ∧ ∃ x ∈ s, ∃ y ∈ s, x ≠ y := by
  rintro ⟨s, hs, x, hx, y, hy, hxy⟩
  exact hxy (padic_isPathConnected_subsingleton hs hx hy)

/-! ## 2. Path-connectedness is universal, the paper log comparison is not -/

/-- A universally true relation cannot imply a relation that fails somewhere. -/
theorem universal_relation_not_imply
    {α : Type*} (P Q : α → α → Prop)
    (hall : ∀ a b, P a b) (hfail : ∃ a b, ¬ Q a b) :
    ¬ ∀ a b, P a b → Q a b := by
  rintro h
  obtain ⟨a, b, hb⟩ := hfail
  exact hb (h a b (hall a b))

/-- The one-factor exponent log of the paper shape: -(sum c) * log p.
This is the formula of S864.paperLambdaOLogVolume for the actual one-factor
index qVFamTensorV = Unit. -/
def exponentLog (P : ℝ) (c : Unit → ℝ) : ℝ :=
  -((∑ _ : Unit, c ()) * Real.log P)

theorem exponentLog_zero (P : ℝ) : exponentLog P 0 = 0 := by
  simp [exponentLog]

theorem exponentLog_one (P : ℝ) : exponentLog P (fun _ => 1) = -Real.log P := by
  simp [exponentLog]

/-- Path-connectedness does not imply the directional log comparison.
The exponent space is path-connected, but the comparison holds only in one
direction; a symmetric predicate cannot select that direction. -/
theorem path_connected_does_not_imply_log_comparison
    (P : ℝ) (hP : 1 < P) :
    (∀ a b : Unit → ℝ, Nonempty (Path a b)) ∧
      ¬ ∀ a b : Unit → ℝ,
        Nonempty (Path a b) → exponentLog P a ≤ exponentLog P b := by
  constructor
  · intro a b
    exact PathConnectedSpace.joined a b
  · apply universal_relation_not_imply
      (fun a b : Unit → ℝ => Nonempty (Path a b))
      (fun a b : Unit → ℝ => exponentLog P a ≤ exponentLog P b)
      (fun a b => PathConnectedSpace.joined a b)
    refine ⟨0, fun _ => 1, ?_⟩
    rw [exponentLog_zero, exponentLog_one]
    exact not_le.mpr (neg_neg_of_pos (Real.log_pos hP))

#print axioms no_homeomorphism_invariant_padic_log
#print axioms padic_path_eq
#print axioms padic_isPathConnected_subsingleton
#print axioms path_connected_does_not_imply_log_comparison

end LeanFormal.IUT.XiFPaper.W8ConfigurationSpaceNoGoActual

end