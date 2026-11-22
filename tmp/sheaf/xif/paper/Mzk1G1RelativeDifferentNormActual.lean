/- H-T 8.2 (batch4a): the relative-different norm identity, isolated as a named data record
with explicit provenance, and the resulting bound on the different term used in route F2. -/
import tmp.sheaf.xif.paper.Mzk1G1ConductorDifferentCancellationCoreActual
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1RelativeDifferentNormActual

open NumberField
open LeanFormal.IUT.XiFPaper.Mzk1G1ConductorDifferentCancellationActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ConductorDifferentCancellationCoreActual

universe u

/-- The relative-different norm identity for a pair of number fields K ⊆ L, together with the
per-place different data.

hlog : log |N(different(O_K,O_L))| = sum over the places w of L of
       delta_{w/v} f_{w/v} log Nv  (the product formula for the norm of the relative
       different in a Dedekind extension).  Provenance: standard Dedekind-domain norm/different
       computation; it is NOT YET PROVED in this file and the record is NO INHABITANT.

hLdim : [L:Q] agrees with the Ldim field of the place data. -/
structure RelativeDifferentNormData (K : Type u) [Field K] [NumberField K] (L : Type u)
    [Field L] [NumberField L] [Algebra K L] [Module.Finite (𝓞 K) (𝓞 L)] where
  D : LocalConductorDifferentData
  hLdim : (D.Ldim : ℝ) = (Module.finrank ℚ L : ℝ)
  hlog : Real.log ((Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L)) : ℕ) : ℝ) =
    ∑ w, ((D.differentExponent w : ℝ) * (D.f w : ℝ) * D.logNv w)

/-- The different term is bounded by log |N(different(O_K,O_L))| / [L:Q], using the
relative-different norm identity (the inequality in the hdifferent field of F2PlaceWitness). -/
theorem differentTerm_le_log_absNorm (K : Type u) [Field K] [NumberField K] (L : Type u)
    [Field L] [NumberField L] [Algebra K L] [Module.Finite (𝓞 K) (𝓞 L)]
    (A : RelativeDifferentNormData K L) :
    differentTerm A.D ≤
      Real.log ((Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L)) : ℕ) : ℝ) /
        (Module.finrank ℚ L : ℝ) := by
  unfold differentTerm
  rw [A.hlog, ← A.hLdim]
  apply le_of_eq
  rw [div_eq_mul_inv, div_eq_mul_inv, one_mul]
  ring

#print axioms differentTerm_le_log_absNorm
end LeanFormal.IUT.XiFPaper.Mzk1G1RelativeDifferentNormActual
