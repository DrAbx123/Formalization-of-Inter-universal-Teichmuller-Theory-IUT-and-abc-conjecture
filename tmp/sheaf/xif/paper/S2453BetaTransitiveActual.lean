import tmp.sheaf.xif.paper.S2446D5FinalActual
import tmp.sheaf.xif.paper.S2339FbarFactorsActual
import tmp.sheaf.xif.paper.S2217DedekindFrobTheoremActual
noncomputable section
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual
open LeanFormal.IUT.XiFPaper.S2397RootFactorMapActual
open LeanFormal.IUT.XiFPaper.S2425PermBarInvarianceActual
open LeanFormal.IUT.XiFPaper.S2446D5FinalActual
open LeanFormal.IUT.XiFPaper.S2339FbarFactorsActual
namespace LeanFormal.IUT.XiFPaper.S2453BetaTransitiveActual
attribute [local instance] Ideal.Quotient.field
variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
variable (f : (RingOfIntegers K)[X]) (p : Ideal (RingOfIntegers K)) [hp : p.IsMaximal]
  (P : Ideal (RingOfIntegers L)) [hP : P.IsPrime] [hPover : P.LiesOver p]
  (hmonic : f.Monic) (hsep : (fbar f p).Separable)
  (hsplit : (f.map (algebraMap (RingOfIntegers K) L)).Splits)
local instance : DecidableEq ((RingOfIntegers K) ⧸ p) := Classical.decEq _

/-- The subtype of normalized irreducible factors of the reduction `fbar f p`. -/
abbrev beta : Type :=
  {g : ((RingOfIntegers K) ⧸ p)[X] //
    g ∈ UniqueFactorizationMonoid.normalizedFactors (fbar f p)}

include hp hP hPover hmonic in
/-- The subtype `beta` of normalized irreducible factors is a fintype. -/
@[reducible] noncomputable def s2453Beta_fintype : Fintype (beta K f p) := by
  classical
  let M := UniqueFactorizationMonoid.normalizedFactors (fbar f p)
  have hset : ({g : ((RingOfIntegers K) ⧸ p)[X] | g ∈ M} : Set _) =
      (M.toFinset : Set _) := by
    ext g
    simp
  have hfin : ({g : ((RingOfIntegers K) ⧸ p)[X] | g ∈ M} : Set _).Finite := by
    rw [hset]
    exact Finset.finite_toSet _
  exact Set.Finite.fintype hfin
include hp hP hPover in
@[simp]
theorem s2453PermBar_val (x : (fbar f p).rootSet ((RingOfIntegers L) ⧸ P)) :
    (permBar (f := f) p P x).1 = frobBar p P x.1 := rfl
include hp hP hPover in
theorem s2453PermBar_pow_apply (n : Nat)
    (x : (fbar f p).rootSet ((RingOfIntegers L) ⧸ P)) :
    ((permBar (f := f) p P ^ n) x).1 = (frobBar p P)^[n] x.1 := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Equiv.Perm.mul_apply]
      change ((permBar (f := f) p P ^ n) (permBar (f := f) p P x)).1 = _
      rw [ih (permBar (f := f) p P x), s2453PermBar_val]
      rw [← Function.iterate_succ_apply]
include hp hP hPover hmonic hsep hsplit in
theorem s2453Fibre_transitive
    (b : beta K f p)
    (x y : (fbar f p).rootSet ((RingOfIntegers L) ⧸ P))
    (hx : s2425RootFactor f p P hmonic hsep x = b)
    (hy : s2425RootFactor f p P hmonic hsep y = b) :
    (permBar (f := f) p P).SameCycle x y := by
  classical
  haveI : P.IsMaximal := P_isMaximal p P
  have hb := (Polynomial.mem_normalizedFactors_iff (s2397Fbar_ne_zero f p P hmonic)).mp b.2
  obtain ⟨hb_irr, hb_monic, hb_dvd⟩ := hb
  have hxmin : minpoly ((RingOfIntegers K) ⧸ p) x.1 = b.1 := congrArg Subtype.val hx
  have hymin : minpoly ((RingOfIntegers K) ⧸ p) y.1 = b.1 := congrArg Subtype.val hy
  have hxroot : (Polynomial.aeval x.1) b.1 = 0 := by
    rw [← hxmin]
    exact minpoly.aeval _ _
  have hyroot : (Polynomial.aeval y.1) b.1 = 0 := by
    rw [← hymin]
    exact minpoly.aeval _ _
  obtain ⟨n, hn⟩ := s2339FrobTransitive f p P hmonic hsep hsplit hb_monic hb_irr hb_dvd hxroot hyroot
  refine ⟨(n : Int), ?_⟩
  rw [zpow_natCast]
  apply Subtype.ext
  rw [s2453PermBar_pow_apply]
  exact hn
#print axioms s2453Beta_fintype
#print axioms s2453PermBar_pow_apply
#print axioms s2453Fibre_transitive
end LeanFormal.IUT.XiFPaper.S2453BetaTransitiveActual
end
