import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Fiber aggregation for the hbad sum identities

David's hsumF / hsumD rewrite a global sum over primes as a sum over rational primes of the
sum over each fiber.  The only set-theoretic input is that the fibers are pairwise disjoint;
the identity is then Finset.sum_biUnion.

Usage (both hsumF and hsumD): take beta = rational primes, alpha = primes of the ring of
integers, fib p = IsDedekindDomain.primesOverFinset (Ideal.span {p}) (ringOfIntegers), and
hfib the disjointness lemma from the tree.  Then
  sum_global = sum_fiber_aggregate s fib f hfib  composed with
  sum over s.biUnion fib = sum over all primes (covering hypothesis, caller side).
-/

noncomputable section
open Finset

namespace LeanFormal.IUT.XiFPaper.Mzk1ULFiberAggregateActual

/-- Aggregation of a sum over a disjoint union of fibers. -/
theorem sum_fiber_aggregate {alpha beta : Type*} [DecidableEq alpha] [DecidableEq beta]
    (s : Finset beta) (fib : beta → Finset alpha) (f : alpha → ℝ)
    (hfib : (s : Set beta).PairwiseDisjoint fib) :
    ∑ a ∈ s.biUnion fib, f a = ∑ b ∈ s, ∑ a ∈ fib b, f a :=
  Finset.sum_biUnion hfib

/-- The same with the two sides swapped, convenient for rewriting a nested sum into a single
sum over the disjoint union. -/
theorem sum_fiber_aggregate' {alpha beta : Type*} [DecidableEq alpha] [DecidableEq beta]
    (s : Finset beta) (fib : beta → Finset alpha) (f : alpha → ℝ)
    (hfib : (s : Set beta).PairwiseDisjoint fib) :
    (∑ b ∈ s, ∑ a ∈ fib b, f a) = ∑ a ∈ s.biUnion fib, f a :=
  (sum_fiber_aggregate s fib f hfib).symm

/-- Monotonicity companion used by the per-place bound: summing the local quantities dominates
the sum of their lower bounds. -/
theorem sum_le_sum_fiber {alpha beta : Type*} [DecidableEq alpha] [DecidableEq beta]
    (s : Finset beta) (fib : beta → Finset alpha) (f g : alpha → ℝ)
    (h : ∀ a, f a ≤ g a) :
    (∑ b ∈ s, ∑ a ∈ fib b, f a) ≤ ∑ b ∈ s, ∑ a ∈ fib b, g a :=
  Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun a _ => h a

#print axioms sum_fiber_aggregate
#print axioms sum_fiber_aggregate'
#print axioms sum_le_sum_fiber
/-! ### Filter form

The consumer may prefer a filter on a finset of primes to the biUnion form; the filter form is
Finset.sum_fiberwise_of_maps_to. -/

/-- Filter form of the fiber aggregation. -/
theorem sum_filter_fiber {alpha beta : Type*} [DecidableEq alpha] [DecidableEq beta]
    (s : Finset alpha) (t : Finset beta) (g : alpha → beta) (f : alpha → ℝ)
    (h : ∀ x ∈ s, g x ∈ t) :
    ∑ y ∈ t, ∑ x ∈ s.filter (fun x => g x = y), f x = ∑ x ∈ s, f x :=
  Finset.sum_fiberwise_of_maps_to h f

/-- The same in the rewriting direction. -/
theorem sum_eq_sum_filter_fiber {alpha beta : Type*} [DecidableEq alpha] [DecidableEq beta]
    (s : Finset alpha) (t : Finset beta) (g : alpha → beta) (f : alpha → ℝ)
    (h : ∀ x ∈ s, g x ∈ t) :
    ∑ x ∈ s, f x = ∑ y ∈ t, ∑ x ∈ s.filter (fun x => g x = y), f x :=
  (sum_filter_fiber s t g f h).symm

/-- Pointwise-bound version of the filter form. -/
theorem sum_le_sum_filter_fiber {alpha beta : Type*} [DecidableEq alpha] [DecidableEq beta]
    (s : Finset alpha) (t : Finset beta) (g : alpha → beta) (f f' : alpha → ℝ)
    (h : ∀ x ∈ s, g x ∈ t) (hle : ∀ x, f x ≤ f' x) :
    (∑ y ∈ t, ∑ x ∈ s.filter (fun x => g x = y), f x)
      ≤ ∑ y ∈ t, ∑ x ∈ s.filter (fun x => g x = y), f' x :=
  Finset.sum_le_sum fun y _ => Finset.sum_le_sum fun x _ => hle x

#print axioms sum_filter_fiber
#print axioms sum_eq_sum_filter_fiber
#print axioms sum_le_sum_filter_fiber
end LeanFormal.IUT.XiFPaper.Mzk1ULFiberAggregateActual