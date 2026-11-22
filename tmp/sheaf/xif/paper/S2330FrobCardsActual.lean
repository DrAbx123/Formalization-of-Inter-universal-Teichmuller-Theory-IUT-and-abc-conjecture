import tmp.sheaf.xif.paper.S2318FrobTransitiveActual
import Mathlib.Dynamics.PeriodicPts.Defs
noncomputable section
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace LeanFormal.IUT.XiFPaper.S2330FrobCardsActual

attribute [local instance] Ideal.Quotient.field
open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual
open LeanFormal.IUT.XiFPaper.S2318FrobTransitiveActual
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
variable (f : (RingOfIntegers K)[X]) (p : Ideal (RingOfIntegers K)) [hp : p.IsMaximal]
  (P : Ideal (RingOfIntegers L)) [hP : P.IsPrime] [hPover : P.LiesOver p]
  (hmonic : f.Monic) (hsep : (fbar f p).Separable)
  (hsplit : (f.map (algebraMap (RingOfIntegers K) L)).Splits)
include hp hP hPover in
/-- The orbit of a root has exactly natDegree g elements. -/
theorem s2330OrbitCard {g : ((RingOfIntegers K) ⧸ p)[X]} (hg : g.Monic)
    (hirr : Irreducible g) {x : (RingOfIntegers L) ⧸ P} (hx : aeval x g = 0) :
    (s2318Orbit p P x).ncard = g.natDegree := by
  classical
  let d := g.natDegree
  have hdpos : 0 < d := by
    have h := @Irreducible.natDegree_pos ((RingOfIntegers K) ⧸ p) _ g hirr
    simpa [d] using h
  have hper : Function.IsPeriodicPt (frobBar p P) d x := by
    exact frobBar_iterate_natDegree p P hg hirr hx
  let img : Finset ((RingOfIntegers L) ⧸ P) :=
    (Finset.range d).image (fun n => (frobBar p P)^[n] x)
  have hset : s2318Orbit p P x = (img : Set ((RingOfIntegers L) ⧸ P)) := by
    ext y
    constructor
    · rintro ⟨n, rfl⟩
      rw [Finset.mem_coe, Finset.mem_image]
      refine ⟨n % d, Finset.mem_range.mpr (Nat.mod_lt _ hdpos), ?_⟩
      exact hper.iterate_mod_apply n
    · intro hy
      rw [Finset.mem_coe, Finset.mem_image] at hy
      rcases hy with ⟨n, hn, rfl⟩
      exact ⟨n, rfl⟩
  have hcard : img.card = d := by
    have hinj : Set.InjOn (fun n => (frobBar p P)^[n] x) (Finset.range d) := by
      intro a ha b hb hab
      have ha' : a < d := Finset.mem_range.mp ha
      have hb' : b < d := Finset.mem_range.mp hb
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have hcancel : (frobBar p P)^[b - a] x = x :=
          Function.iterate_cancel (frobBar_injective p P) hab.symm
        exact frobBar_iterate_ne_self p P hg hirr hx (by omega) (by omega) hcancel
      · have hcancel : (frobBar p P)^[a - b] x = x :=
          Function.iterate_cancel (frobBar_injective p P) hab
        exact frobBar_iterate_ne_self p P hg hirr hx (by omega) (by omega) hcancel
    rw [Finset.card_image_of_injOn hinj]
    simp [d]
  rw [hset, Set.ncard_coe_finset, hcard]
/-- The fibre is the root set of g, so separable splitting g gives cardinal
natDegree g. -/
theorem s2330FiberCard_of_splits_separable
    {g : ((RingOfIntegers K) ⧸ p)[X]} (hg : g.Monic)
    (hsepg : g.Separable)
    (hsplitg : (g.map (algebraMap ((RingOfIntegers K) ⧸ p) ((RingOfIntegers L) ⧸ P))).Splits) :
    (s2318Fiber p P g).ncard = g.natDegree := by
  classical
  haveI : P.IsMaximal := P_isMaximal p P
  letI : Field ((RingOfIntegers L) ⧸ P) := Ideal.Quotient.field P
  letI : Algebra ((RingOfIntegers K) ⧸ p) ((RingOfIntegers L) ⧸ P) :=
    Ideal.Quotient.algebraOfLiesOver P p
  have hroot : s2318Fiber p P g = (g.rootSet ((RingOfIntegers L) ⧸ P)) := by
    ext y
    rw [show y ∈ s2318Fiber p P g ↔ aeval y g = 0 from Iff.rfl]
    rw [Polynomial.mem_rootSet']
    constructor
    · intro h
      exact ⟨(hg.map (algebraMap ((RingOfIntegers K) ⧸ p) ((RingOfIntegers L) ⧸ P))).ne_zero, h⟩
    · exact fun h => h.2
  rw [hroot]
  have hcard := Polynomial.card_rootSet_eq_natDegree
    (F := (RingOfIntegers K) ⧸ p) (K := (RingOfIntegers L) ⧸ P) hsepg hsplitg
  simpa using hcard
/-- Conditional transitivity from splits/separable of g. -/
theorem s2330FrobTransitive_of_splits_separable
    {g : ((RingOfIntegers K) ⧸ p)[X]} (hg : g.Monic) (hirr : Irreducible g)
    (hsepg : g.Separable)
    (hsplitg : (g.map (algebraMap ((RingOfIntegers K) ⧸ p) ((RingOfIntegers L) ⧸ P))).Splits)
    {x y : (RingOfIntegers L) ⧸ P} (hx : aeval x g = 0) (hy : aeval y g = 0) :
    ∃ n : ℕ, (frobBar p P)^[n] x = y := by
  exact s2318FrobTransitive_of_card p P hg hirr hx hy
    (s2330OrbitCard p P hg hirr hx) (s2330FiberCard_of_splits_separable p P hg hsepg hsplitg)
#print axioms s2330OrbitCard
#print axioms s2330FiberCard_of_splits_separable
#print axioms s2330FrobTransitive_of_splits_separable
end LeanFormal.IUT.XiFPaper.S2330FrobCardsActual
end
