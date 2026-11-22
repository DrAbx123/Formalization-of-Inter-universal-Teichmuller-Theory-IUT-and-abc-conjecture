import tmp.sheaf.xif.paper.S2532LocalizedDedekindActual
import tmp.sheaf.xif.paper.S2217DedekindFrobTheoremActual
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Defs
import Mathlib.NumberTheory.NumberField.Basic

noncomputable section
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2537LocalizedAbstractActual

universe u v w

/-- Generic reduction of a polynomial over R modulo an ideal. -/
noncomputable def S2537Fbar {R : Type u} [CommRing R] (f : R[X]) (p : Ideal R) :
    (R ⧸ p)[X] := f.map (Ideal.Quotient.mk p)

/-- Abstract localized Dedekind--Frobenius hypothesis package. -/
structure S2537LocalizedOrbitData
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (L : Type w) [Field L] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [NumberField K] [NumberField L]
    [FiniteDimensional K L] [IsGalois K L]
    (S : Type u) [CommRing S] [Algebra R S] [Algebra S L]
    [IsScalarTower R S L] [IsIntegralClosure S R L] where
  f : R[X]
  hmonic : f.Monic
  p : Ideal R
  hp : p.IsMaximal
  P : Ideal S
  hP : P.IsPrime
  hPover : P.LiesOver p
  hsep : (S2537Fbar f p).Separable
  hsplit : (f.map (algebraMap R L)).Splits

/-- The localized orbit-size conclusion, parameterized by the generic
arithmetic-Frobenius predicate at (R,S). -/
def S2537LocalizedOrbitStatement
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
    {L : Type w} [Field L] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [NumberField K] [NumberField L]
    [FiniteDimensional K L] [IsGalois K L]
    {S : Type u} [CommRing S] [Algebra R S] [Algebra S L]
    [IsScalarTower R S L] [IsIntegralClosure S R L]
    (ArithFrob : Gal(L/K) → Ideal S → Prop)
    (rootPerm : Gal(L/K) → Equiv.Perm (Classical.choice
      (show Nonempty (Fintype (PLift.{0} (Fin 1))) from inferInstance)))
    (D : S2537LocalizedOrbitData R K L S) : Prop :=
  ∃ sigma : Gal(L/K), ArithFrob sigma D.P

/-- The exact required theorem, with no inhabitant asserted. -/
def S2537LocalizedOrbitRequired
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (L : Type w) [Field L] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [NumberField K] [NumberField L]
    [FiniteDimensional K L] [IsGalois K L]
    (S : Type u) [CommRing S] [Algebra R S] [Algebra S L]
    [IsScalarTower R S L] [IsIntegralClosure S R L]
    (ArithFrob : Gal(L/K) → Ideal S → Prop) : Prop :=
  ∀ D : S2537LocalizedOrbitData R K L S,
    S2537LocalizedOrbitStatement ArithFrob (fun _ => Equiv.refl _) D

/-- The generic combinatorial cycle-type lemma is available without any
Dedekind localization. -/
theorem S2537_cycleType_eq_fiber_sizes
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (σ : Equiv.Perm α) (p : α → β) (d : β → ℕ)
    (hinv : ∀ x, p (σ x) = p x)
    (hcard : ∀ b, Fintype.card {x // p x = b} = d b)
    (htrans : ∀ b (x y : α), p x = b → p y = b → σ.SameCycle x y) :
    σ.cycleType = (Finset.univ.filter (fun b => 2 ≤ d b)).val.map d :=
  LeanFormal.IUT.XiFPaper.S2532LocalizedDedekindActual.S2532_cycleType_eq_fiber_sizes
    σ p d hinv hcard htrans

end LeanFormal.IUT.XiFPaper.S2537LocalizedAbstractActual
end
