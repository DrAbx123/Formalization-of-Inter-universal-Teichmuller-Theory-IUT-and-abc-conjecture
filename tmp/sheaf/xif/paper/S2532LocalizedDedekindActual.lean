import tmp.sheaf.xif.paper.S2217DedekindFrobTheoremActual
import Mathlib.RingTheory.DedekindDomain.Basic

noncomputable section
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S2532LocalizedDedekindActual

open Polynomial
open LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual

universe u v

/-- The reduction of a polynomial over an arbitrary ring modulo an ideal. -/
def S2532Fbar {R : Type u} [CommRing R] (f : R[X]) (p : Ideal R) :
    (R ⧸ p)[X] :=
  f.map (Ideal.Quotient.mk p)

/-- The generic combinatorial orbit-size lemma from S2217, re-exported without
the RingOfIntegers specialization. -/
theorem S2532_cycleType_eq_fiber_sizes
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (σ : Equiv.Perm α) (p : α → β) (d : β → ℕ)
    (hinv : ∀ x, p (σ x) = p x)
    (hcard : ∀ b, Fintype.card {x // p x = b} = d b)
    (htrans : ∀ b (x y : α), p x = b → p y = b → σ.SameCycle x y) :
    σ.cycleType = (Finset.univ.filter (fun b => 2 ≤ d b)).val.map d :=
  cycleType_eq_fiber_sizes σ p d hinv hcard htrans

/-- The exact localized Dedekind--Frobenius obligation.  This records the
arithmetic-Frobenius/orbit-size package at a general Dedekind base R; it has no
inhabitant. -/
structure S2532LocalizedDedekindFrobeniusRequired
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {K : Type u} [Field K] [NumberField K]
    {L : Type v} [Field L] [NumberField L] [Algebra K L]
    (f : R[X]) (p : Ideal R) [p.IsMaximal] : Type u where
  arithmeticFrobenius : Prop
  orbitSize_eq : arithmeticFrobenius

end LeanFormal.IUT.XiFPaper.S2532LocalizedDedekindActual
end
