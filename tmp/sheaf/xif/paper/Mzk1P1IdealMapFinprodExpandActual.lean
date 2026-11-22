/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.RingTheory.DedekindDomain.Factorization
import tmp.sheaf.xif.paper.Mzk1P1IdealMapFinsetProdActual
import Mathlib.Tactic

/-! # P1: finite-support expansion of the ideal factorization + map -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1IdealMapFinprodExpandActual

open IsDedekindDomain

variable {R : Type} [CommRing R] [IsDedekindDomain R]

/-- The factorization of a nonzero ideal as a Finset product of the `maxPowDividing`
prime powers (finite-support expansion of `Ideal.finprod_heightOneSpectrum_factorization`). -/
-- `calc`/`.trans` form avoids the dependent-motive `rw` failure.
theorem ideal_eq_finset_prod_maxPowDividing {I : Ideal R} (hI : I ≠ 0) :
    I = ∏ i ∈ (Ideal.hasFiniteMulSupport (R := R) hI).toFinset,
      i.maxPowDividing I :=
  (Ideal.finprod_heightOneSpectrum_factorization hI).symm.trans
    (finprod_eq_prod (fun i : HeightOneSpectrum R => i.maxPowDividing I)
      (Ideal.hasFiniteMulSupport hI))

/-- `Ideal.map` of a nonzero ideal is the Finset product of the maps of the prime-power
factors (hypothesis form, to avoid dependent-motive rewriting). -/
theorem ideal_map_eq_finset_prod_map_of_eq {S : Type} [CommRing S] (f : R →+* S)
    {I : Ideal R} (s : Finset (HeightOneSpectrum R))
    (hI : I = ∏ i ∈ s, i.maxPowDividing I) :
    Ideal.map f I = ∏ i ∈ s, Ideal.map f (i.maxPowDividing I) := by
  conv_lhs => rw [hI]
  exact LeanFormal.IUT.XiFPaper.Mzk1P1IdealMapFinsetProdActual.ideal_map_finset_prod f s _

/-- `Ideal.map` of a nonzero ideal is the Finset product of the maps of the prime-power
factors. -/
theorem ideal_map_eq_finset_prod_map {S : Type} [CommRing S] (f : R →+* S)
    {I : Ideal R} (hI : I ≠ 0) :
    Ideal.map f I =
      ∏ i ∈ (Ideal.hasFiniteMulSupport (R := R) hI).toFinset,
        Ideal.map f (i.maxPowDividing I) :=
  ideal_map_eq_finset_prod_map_of_eq f _ (ideal_eq_finset_prod_maxPowDividing hI)

def finprodExpandRows : List (String × String × String) :=
  [ ("ideal_eq_finset_prod_maxPowDividing", "I = prod over finite support of maxPowDividing", "PROVED"),
    ("ideal_map_eq_finset_prod_map_of_eq", "hypothesis form", "PROVED"),
    ("ideal_map_eq_finset_prod_map", "Ideal.map I = prod of maps (finite support)", "PROVED") ]

theorem finprodExpandRows_length : finprodExpandRows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P1IdealMapFinprodExpandActual

end