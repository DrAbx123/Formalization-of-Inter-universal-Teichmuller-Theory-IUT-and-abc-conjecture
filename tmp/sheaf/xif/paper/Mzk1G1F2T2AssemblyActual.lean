/- Route 8.2 assembly: T2 gives the per-place different lower bound (ramification index - 1
<= different multiplicity), hence the hdelta input of the conductor/different cancellation;
the generic cancellation bound then follows from the DONE conductor core and the relative
different norm bound. -/
import tmp.sheaf.xif.paper.Mzk1G1F2T2Actual
import tmp.sheaf.xif.paper.Mzk1G1PlaceDataActual
import tmp.sheaf.xif.paper.Mzk1G1RelativeDifferentNormActual
import tmp.sheaf.xif.paper.Mzk1G1ConductorDifferentCancellationCoreActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1F2T2AssemblyActual

open NumberField
open UniqueFactorizationMonoid
open LeanFormal.IUT.XiFPaper.Mzk1G1PlaceDataActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ConductorDifferentCancellationCoreActual
open LeanFormal.IUT.XiFPaper.Mzk1G1RelativeDifferentNormActual
open LeanFormal.IUT.XiFPaper.Mzk1G1F2T2Actual

universe u

section

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [Module.Finite (𝓞 K) (𝓞 L)]

/-- Generic conductor-different cancellation: the conductor difference is bounded by the
normalized log absolute norm of the relative different, using hdelta (from T2) and the
relative-different norm identity. -/
theorem conductorDifference_le_log_absNorm (A : RelativeDifferentNormData K L)
    (hdelta : ∀ w, A.D.e w - 1 ≤ A.D.differentExponent w) :
    conductorDifference A.D ≤
      Real.log ((Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L)) : ℕ) : ℝ) /
        (Module.finrank ℚ L : ℝ) :=
  le_trans (conductorDifference_le_differentTerm A.D hdelta)
    (differentTerm_le_log_absNorm K L A)

/-- The place data with the actual relative-different exponents delta(P). -/
noncomputable def placeDataDifferent (p : Ideal (𝓞 K)) [p.IsMaximal] (hp : p ≠ ⊥) :
    LocalConductorDifferentData :=
  placeData (K := K) (L := L) p hp
    (fun P => (normalizedFactors (differentIdeal (𝓞 K) (𝓞 L))).count P)

/-- T2 supplies the hdelta field of the place data: ramification index - 1 is at most the
different multiplicity. -/
theorem placeDataDifferent_hdelta (p : Ideal (𝓞 K)) [p.IsMaximal] (hp : p ≠ ⊥) :
    ∀ w, (placeDataDifferent (K := K) (L := L) p hp).e w - 1 ≤
      (placeDataDifferent (K := K) (L := L) p hp).differentExponent w := by
  intro w
  have hmem : w.1 ∈ p.primesOver (𝓞 L) := w.2
  exact T2_relative_different_count (K := K) (L := L) p hp w.1 hmem.2

end

#print axioms conductorDifference_le_log_absNorm
#print axioms placeDataDifferent_hdelta
end LeanFormal.IUT.XiFPaper.Mzk1G1F2T2AssemblyActual
