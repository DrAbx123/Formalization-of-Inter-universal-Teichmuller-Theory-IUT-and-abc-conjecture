/- H-T 8.2 (batch4b): the per-place conductor data built from actual number-field places.
Above a maximal ideal p of O_K, the places P of O_L are the primes in p.primesOver (O_L);
e = ramificationIdx, f = inertiaDeg, log Nv = log |N(p)|.  The different exponent delta is an
input function (the multiplicity of P in the relative different ideal); its actual construction
is provenance-documented and NO INHABITANT in this file. -/
import tmp.sheaf.xif.paper.Mzk1G1ConductorDifferentCancellationCoreActual
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.Over
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PlaceDataActual

open NumberField
open LeanFormal.IUT.XiFPaper.Mzk1G1ConductorDifferentCancellationCoreActual

universe u

/-- A finite place of the base number field K, given by a maximal ideal of O_K. -/
structure KPlace (K : Type u) [Field K] [NumberField K] where
  p : Ideal (𝓞 K)
  p_ne_bot : p ≠ ⊥
  p_max : p.IsMaximal

section

variable {K : Type u} [Field K] [NumberField K]
variable {L : Type u} [Field L] [NumberField L] [Algebra K L]
variable [Module.Finite (𝓞 K) (𝓞 L)]

/-- The per-place conductor/different data above a maximal ideal p of O_K, with the different
exponents supplied by delta.

delta : O_L-ideals → ℕ is meant to be the multiplicity of the prime P in the relative different
ideal differentIdeal (O_K) (O_L).  Its construction via the Dedekind factorization API is NOT
proved here and the record stays NO INHABITANT until that is done; the other fields are actual:
W = primesOver p, e = ramificationIdx, f = inertiaDeg, logNv = log |N(p)|, Ldim = [L:Q]. -/
def placeData (p : Ideal (𝓞 K)) [hp : p.IsMaximal] (hp_ne_bot : p ≠ ⊥)
    (delta : Ideal (𝓞 L) → ℕ) :
    LocalConductorDifferentData where
  W := p.primesOver (𝓞 L)
  Ldim := Module.finrank ℚ L
  Ldim_pos := Module.finrank_pos
  e := fun P =>
    letI : P.1.IsPrime := (Ideal.isMaximal_of_mem_primesOver P.2).isPrime
    P.1.ramificationIdx (𝓞 K)
  e_pos := fun P => by
    haveI : P.1.IsPrime := (Ideal.isMaximal_of_mem_primesOver P.2).isPrime
    exact Ideal.ramificationIdx_pos P.1 (𝓞 K)
  f := fun P => P.1.inertiaDeg (𝓞 K)
  logNv := fun _ => Real.log ((Ideal.absNorm p : ℕ) : ℝ)
  logNv_nonneg := fun _ => Real.log_natCast_nonneg _
  differentExponent := fun P => delta P.1

end

#print axioms placeData
end LeanFormal.IUT.XiFPaper.Mzk1G1PlaceDataActual
