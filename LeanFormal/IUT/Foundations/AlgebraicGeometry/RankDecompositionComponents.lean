import LeanFormal.IUT.Foundations.AlgebraicGeometry.RankDecompositionFixedPoints
import LeanFormal.IUT.Foundations.AlgebraicGeometry.CompleteOrthogonalIdempotentsPi
import Mathlib.Tactic

open AlgebraicGeometry CategoryTheory
open Module
open RankDecompositionFixedPoints
open scoped BigOperators

noncomputable section

namespace RankDecompositionComponents

universe u

variable {R A G : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G R A]
  [Module.Finite R A] [Module.Projective R A]

/-- The finite set of possible ranks of A at primes. -/
noncomputable def rankIndex : Finset ℕ :=
  (rankAtStalk_finite_range (R := R) (M := A)).toFinset

noncomputable def eRank (n : ↑(rankIndex (R := R) (A := A))) : R :=
  rankComponentIdempotent (R := R) (A := A) n.1

lemma rank_eq_of_mem_basicOpen (n : ↑(rankIndex (R := R) (A := A)))
    {p : PrimeSpectrum R} (hp : p ∈ PrimeSpectrum.basicOpen (eRank (R := R) (A := A) n)) :
    Module.rankAtStalk (R := R) A p = n.1 := by
  have hset := rankComponent_basicOpen (R := R) (A := A) n.1
  exact (Set.ext_iff.mp hset p).mp hp




/-- The rank idempotents are pairwise orthogonal. -/
lemma eRank_orthogonal : OrthogonalIdempotents (eRank (R := R) (A := A)) := by
  refine ⟨fun n => rankComponentIdempotent_isIdempotent (R := R) (A := A) n.1, ?_⟩
  intro i j hij
  have hdisj : Disjoint (PrimeSpectrum.basicOpen (eRank (R := R) (A := A) i) : Set (PrimeSpectrum R))
      (PrimeSpectrum.basicOpen (eRank (R := R) (A := A) j) : Set (PrimeSpectrum R)) := by
    rw [Set.disjoint_iff]
    intro p hp
    exact hij (Subtype.ext ((rank_eq_of_mem_basicOpen (R := R) (A := A) i hp.1).symm.trans
      (rank_eq_of_mem_basicOpen (R := R) (A := A) j hp.2)))
  have hbot : PrimeSpectrum.basicOpen (eRank (R := R) (A := A) i *
      eRank (R := R) (A := A) j) = ⊥ := by
    rw [PrimeSpectrum.basicOpen_mul]
    ext p
    simp only [TopologicalSpace.Opens.coe_inf, TopologicalSpace.Opens.coe_bot,
      Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    exact fun hp => hdisj.le_bot hp
  have hnil : IsNilpotent (eRank (R := R) (A := A) i *
      eRank (R := R) (A := A) j) :=
    (PrimeSpectrum.basicOpen_eq_bot_iff _).mp hbot
  exact IsIdempotentElem.eq_zero_of_isNilpotent
    ((rankComponentIdempotent_isIdempotent (R := R) (A := A) i.1).mul
      (rankComponentIdempotent_isIdempotent (R := R) (A := A) j.1)) hnil
/-- The rank-idempotent basic opens cover Spec R. -/
lemma eRank_iSup_basicOpen_eq_top :
    (⨆ n : ↑(rankIndex (R := R) (A := A)),
      PrimeSpectrum.basicOpen (eRank (R := R) (A := A) n)) = ⊤ := by
  apply top_unique
  intro p hp
  rw [TopologicalSpace.Opens.mem_iSup]
  have hmem : Module.rankAtStalk (R := R) A p ∈ rankIndex (R := R) (A := A) := by
    rw [rankIndex]
    exact (Set.Finite.mem_toFinset _).mpr ⟨p, rfl⟩
  refine ⟨⟨Module.rankAtStalk (R := R) A p, hmem⟩, ?_⟩
  have h : p ∈ (PrimeSpectrum.basicOpen
      (rankComponentIdempotent (R := R) (A := A) (Module.rankAtStalk (R := R) A p)) :
        Set (PrimeSpectrum R)) := by
    rw [rankComponent_basicOpen]
    rfl
  simpa [eRank] using h

/-- The rank idempotents span the unit ideal. -/
lemma eRank_span_eq_top :
    Ideal.span (Set.range (eRank (R := R) (A := A))) = ⊤ :=
  (PrimeSpectrum.iSup_basicOpen_eq_top_iff).mp
    (eRank_iSup_basicOpen_eq_top (R := R) (A := A))

end RankDecompositionComponents
