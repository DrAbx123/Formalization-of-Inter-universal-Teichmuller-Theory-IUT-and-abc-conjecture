import tmp.sheaf.xif.paper.S2217DedekindFrobTheoremActual
import tmp.sheaf.xif.paper.S2309SubfieldUniqueActual
noncomputable section
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
namespace LeanFormal.IUT.XiFPaper.S2318FrobTransitiveActual
open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
variable (f : (RingOfIntegers K)[X]) (p : Ideal (RingOfIntegers K)) [hp : p.IsMaximal]
  (P : Ideal (RingOfIntegers L)) [hP : P.IsPrime] [hPover : P.LiesOver p]
  (hmonic : f.Monic) (hsep : (fbar f p).Separable)
  (hsplit : (f.map (algebraMap (RingOfIntegers K) L)).Splits)
/-- The q-Frobenius orbit of x in the residue field. -/
noncomputable def s2318Orbit (x : (RingOfIntegers L) ⧸ P) : Set ((RingOfIntegers L) ⧸ P) :=
  {y | ∃ n : ℕ, (frobBar p P)^[n] x = y}
/-- The minpoly fibre of a root x: roots of g in the residue field. -/
def s2318Fiber (g : ((RingOfIntegers K) ⧸ p)[X]) : Set ((RingOfIntegers L) ⧸ P) :=
  {y | aeval y g = 0}
include hp hP hPover in
/-- If the orbit has exactly natDegree g elements and the minpoly fibre also has
natDegree g elements, then Frobenius is transitive on the fibre. -/
theorem s2318FrobTransitive_of_card
    {g : ((RingOfIntegers K) ⧸ p)[X]} (hg : g.Monic) (hirr : Irreducible g)
    {x y : (RingOfIntegers L) ⧸ P} (hx : aeval x g = 0) (hy : aeval y g = 0)
    (horbit : (s2318Orbit p P x).ncard = g.natDegree)
    (hfiber : (s2318Fiber (p:=p) (P:=P) g).ncard = g.natDegree) :
    ∃ n : ℕ, (frobBar p P)^[n] x = y := by
  classical
  haveI : P.IsMaximal := P_isMaximal p P
  haveI : Fintype ((RingOfIntegers L) ⧸ P) := Fintype.ofFinite _
  have hsub : s2318Orbit p P x ⊆ s2318Fiber (p:=p) (P:=P) g := by
    intro z hz
    rcases hz with ⟨n, rfl⟩
    induction n with
    | zero => simpa [s2318Fiber] using hx
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        have hfib : s2318Fiber p P g = {y | aeval y g = 0} := rfl
        rw [hfib] at ih ⊢
        simp only [Set.mem_setOf_eq] at ih ⊢
        rw [aeval_frobBar]
        rw [ih, zero_pow]
        exact Nat.card_pos.ne'
  have heq : s2318Orbit p P x = s2318Fiber (p:=p) (P:=P) g := by
    apply Set.eq_of_subset_of_ncard_le hsub (ht := Set.toFinite _)
    rw [horbit, hfiber]
  have hy' : y ∈ s2318Orbit p P x := by rw [heq]; exact hy
  rcases hy' with ⟨n, hn⟩
  exact ⟨n, hn⟩
/-- Exact missing card input 1: orbit cardinal. -/
def s2318OrbitCard (g : ((RingOfIntegers K) ⧸ p)[X])
    (x : (RingOfIntegers L) ⧸ P) : Prop :=
  (s2318Orbit p P x).ncard = g.natDegree
/-- Exact missing card input 2: minpoly fibre cardinal. -/
def s2318FiberCard (g : ((RingOfIntegers K) ⧸ p)[X]) : Prop :=
  (s2318Fiber (p:=p) (P:=P) g).ncard = g.natDegree
#print axioms s2318FrobTransitive_of_card
end LeanFormal.IUT.XiFPaper.S2318FrobTransitiveActual
end
