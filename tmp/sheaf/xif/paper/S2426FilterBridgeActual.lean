import tmp.sheaf.xif.paper.S2408FiberSizesActual
import tmp.sheaf.xif.paper.S2217DedekindFrobTheoremActual
import tmp.sheaf.xif.paper.S2167DedekindFrobCycleActual
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

/-!
# S2426: the filter bridge from normalized-factor degrees to factor degrees

The Dedekind--Frobenius comparison consumes the multiset of irreducible factor
degrees of the reduction "fbar f p" with the linear factors removed (that is,
Mathlib's cycle type: it never contains 1, see
Equiv.Perm.one_lt_of_mem_cycleType).  The existing files produce this multiset
in two different shapes:

* "factorDegrees (fbar f p)" -- the degrees of all normalized factors
  (S2167), which still contains the 1s;
* "(normalizedFactors (fbar f p)).map d" for a degree function d on normalized
  factors, where d is Polynomial.natDegree (S2217) or the cardinality of the
  minpoly fibre s2408FiberSet (S2408).

This file proves the generic multiset identity which removes the 1s in a single
step, together with its two specialisations.

## Main results

* s2426_filter_two_le_eq_map_filter: for a multiset M and a function
  d : alpha -> Nat which is at least 1 on the members of M,
  (M.map d).filter (2 <= .) = (M.filter (d . != 1)).map d;
* s2426_filter_natDegree_eq_factorDegrees_filter:
  ((normalizedFactors (fbar f p)).map natDegree).filter (2 <= .)
     = (factorDegrees (fbar f p)).filter (. != 1);
* s2426_filter_fiberSizes_eq_factorDegrees_filter: the same identity with
  d g = (s2408FiberSet g).ncard, using s2408FiberSizes_eq_factorDegrees.

No sorry, admit, axiom, opaque declaration or native_decide is used.
-/

noncomputable section
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual
open LeanFormal.IUT.XiFPaper.S2408FiberSizesActual

namespace LeanFormal.IUT.XiFPaper.S2426FilterBridgeActual

attribute [local instance] Ideal.Quotient.field

/-! ## 1. The generic multiset bridge -/

/-- Removing the entries equal to 1 from the image of a multiset under a
positive degree function is the same as first removing the members with degree
1 and then taking the image. -/
theorem s2426_filter_two_le_eq_map_filter {α : Type*} (M : Multiset α) (d : α → ℕ)
    (hd : ∀ a ∈ M, 1 ≤ d a) :
    (M.map d).filter (fun n => 2 ≤ n) = (M.filter (fun a => d a ≠ 1)).map d := by
  classical
  have h1 : (M.map d).filter (fun n => 2 ≤ n) = (M.map d).filter (fun n => n ≠ 1) := by
    apply Multiset.filter_congr
    intro n hn
    obtain ⟨a, ha, hda⟩ := Multiset.mem_map.mp hn
    rw [← hda]
    have hpos : 1 ≤ d a := hd a ha
    omega
  rw [h1, Multiset.filter_map]

/-! ## 2. Specialisation to the degree map natDegree -/

section NatDegree

variable {K : Type*} [NumberField K]
variable (f : (RingOfIntegers K)[X]) (p : Ideal (RingOfIntegers K)) [hp : p.IsMaximal]

/-- Every normalized factor of the reduction of f has degree at least one:
it is irreducible, hence nonconstant. -/
theorem s2426_natDegree_pos_of_mem_normalizedFactors
    {g : ((RingOfIntegers K) ⧸ p)[X]}
    (hg : g ∈ UniqueFactorizationMonoid.normalizedFactors (fbar f p)) :
    1 ≤ g.natDegree :=
  (UniqueFactorizationMonoid.irreducible_of_normalized_factor g hg).natDegree_pos

/-- The definitional unfolding of factorDegrees. -/
theorem s2426_factorDegrees_eq_map_natDegree :
    factorDegrees (fbar f p) =
      (UniqueFactorizationMonoid.normalizedFactors (fbar f p)).map Polynomial.natDegree := by
  unfold factorDegrees
  rfl

/-- The filter bridge for the multiset of normalized factor degrees: keeping the
entries of size at least two is the same as removing the linear factors from the
multiset of all factor degrees. -/
theorem s2426_filter_natDegree_eq_factorDegrees_filter :
    ((UniqueFactorizationMonoid.normalizedFactors (fbar f p)).map Polynomial.natDegree).filter
        (fun n => 2 ≤ n) =
      (factorDegrees (fbar f p)).filter (fun n => n ≠ 1) := by
  classical
  rw [s2426_filter_two_le_eq_map_filter
    (UniqueFactorizationMonoid.normalizedFactors (fbar f p)) Polynomial.natDegree
    (fun g hg => s2426_natDegree_pos_of_mem_normalizedFactors f p hg)]
  rw [s2426_factorDegrees_eq_map_natDegree, Multiset.filter_map]

end NatDegree

/-! ## 3. Specialisation to the minpoly fibre sizes -/

section FiberSizes

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
variable (f : (RingOfIntegers K)[X]) (p : Ideal (RingOfIntegers K)) [hp : p.IsMaximal]
  (P : Ideal (RingOfIntegers L)) [hP : P.IsPrime] [hPover : P.LiesOver p]
  (hmonic : f.Monic) (hsep : (fbar f p).Separable)
  (hsplit : (Polynomial.map (algebraMap (RingOfIntegers K) L) f).Splits)

/-- Every normalized factor has a fibre of at least one root, so its fibre size is
at least one. -/
theorem s2426_ncard_pos_of_mem_normalizedFactors
    {g : ((RingOfIntegers K) ⧸ p)[X]}
    (hg : g ∈ UniqueFactorizationMonoid.normalizedFactors (fbar f p)) :
    1 ≤ (s2408FiberSet (K := K) (L := L) (p := p) (P := P) g).ncard := by
  rw [s2408FiberSet_ncard (K := K) (L := L) (f := f) (hmonic := hmonic) (hsep := hsep)
    (hsplit := hsplit) (p := p) (P := P) (hg := hg)]
  exact s2426_natDegree_pos_of_mem_normalizedFactors f p hg

/-- The filter bridge for the multiset of minpoly fibre sizes: keeping the fibres
of size at least two is the same as removing the linear factors from the multiset
of all factor degrees. -/
theorem s2426_filter_fiberSizes_eq_factorDegrees_filter :
    ((UniqueFactorizationMonoid.normalizedFactors (fbar f p)).map
        (fun g => (s2408FiberSet (K := K) (L := L) (p := p) (P := P) g).ncard)).filter
        (fun n => 2 ≤ n) =
      (factorDegrees (fbar f p)).filter (fun n => n ≠ 1) := by
  classical
  rw [s2426_filter_two_le_eq_map_filter
    (UniqueFactorizationMonoid.normalizedFactors (fbar f p))
    (fun g => (s2408FiberSet (K := K) (L := L) (p := p) (P := P) g).ncard)
    (fun g hg => s2426_ncard_pos_of_mem_normalizedFactors f p P hmonic hsep hsplit hg)]
  rw [← s2408FiberSizes_eq_factorDegrees (K := K) (L := L) (f := f) (hmonic := hmonic)
    (hsep := hsep) (hsplit := hsplit) (p := p) (P := P), Multiset.filter_map]

end FiberSizes

/-! ## 4. Axiom footprint -/

#print axioms s2426_filter_two_le_eq_map_filter
#print axioms s2426_natDegree_pos_of_mem_normalizedFactors
#print axioms s2426_factorDegrees_eq_map_natDegree
#print axioms s2426_filter_natDegree_eq_factorDegrees_filter
#print axioms s2426_ncard_pos_of_mem_normalizedFactors
#print axioms s2426_filter_fiberSizes_eq_factorDegrees_filter

end LeanFormal.IUT.XiFPaper.S2426FilterBridgeActual

end
