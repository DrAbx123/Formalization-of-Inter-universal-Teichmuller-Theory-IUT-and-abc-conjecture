import tmp.sheaf.xif.paper.Mzk1G1LocalHeightCriterionActual
import tmp.sheaf.xif.paper.Mzk1ULPointConductorActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.G1D2InterfaceActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.G1LocalHeightCriterionActual

/-!
# D2 interface: the tripodal dictionary of route section 6.4

Route section 6.4 requires the actual point-field / tripodal-field identification
to supply, for the tripodal Θ-data attached to a Legendre parameter `lam`:

* `log-diff_X(lam) = log d_Ftpd`;
* `log f_Ftpd <= N_D(lam)`, where `N_D(lam)` is the normalized truncated
  conductor of the **point field ℚ(lam)** (not K_V; paper IUT IV L101-109
  log-cond_D, IV L1305-1353 fF conductor, IV L1214-1235 Def 1.9 normalized
  degree; route L564/L615-627), realized as
  `Mzk1ULPointConductorActual.pointND (K := K) lam`;
* `d_mod <= d`, with `d` the fixed degree bound;
* `e*` is bounded by a function of the fixed degree bound only.

This file only records the precise interface (NO INHABITANT): the actual
objects `logDiff`, `dFtpd`, `fFtpd`, `dmod`, `eStar` are to be produced by
the U-C lane from the actual point field, tripodal field and per-place
conductor definitions once the C4 / P6-final display is available.  No
placeholder or arbitrary data is used: every law below is the exact relation
needed by the D4 instantiation of route section 6.4, and the local lane only
consumes this interface after U-C supplies an actual inhabitant.
-/

variable {K : Type*} [Field K] [NumberField K]

/-- The tripodal dictionary interface of route section 6.4: actual local
log-different, tripodal different/conductor data, modulo degree and `e*`
control, related to the normalized truncated conductor `N_D`. -/
structure TripodalDictionary (K : Type*) [Field K] [NumberField K] (d : ℕ) where
  /-- Actual `log-diff_X(lam)` of the tripodal point field. -/
  logDiff : K → ℝ
  /-- Actual `d_Ftpd` of the tripodal field. -/
  dFtpd : K → ℝ
  /-- Actual `f_Ftpd` of the tripodal field. -/
  fFtpd : K → ℝ
  /-- The actual modulo-degree `d_mod` of the display. -/
  dmod : ℕ
  /-- The actual `e*` of the tripodal field. -/
  eStar : K → ℝ
  /-- The degree-function constant controlling `e*`. -/
  Cd : ℝ
  dFtpd_pos : ∀ lam, 0 < dFtpd lam
  fFtpd_pos : ∀ lam, 0 < fFtpd lam
  /-- `log-diff_X(lam) = log d_Ftpd`. -/
  logDiff_eq : ∀ lam, logDiff lam = Real.log (dFtpd lam)
  /-- `log f_Ftpd <= N_D(lam)` against the point-field normalized truncated conductor. -/
  fFtpd_le_conductor : ∀ lam, Real.log (fFtpd lam) ≤ Mzk1ULPointConductorActual.pointND (K := K) lam
  /-- `d_mod <= d` for the fixed degree bound. -/
  dmod_le : dmod ≤ d
  /-- `e*` is controlled by the fixed degree-function constant. -/
  eStar_le : ∀ lam, eStar lam ≤ Cd

/-- The exact relations exported by the D2 interface, in the order used by the
route section 6.4 tripodal dictionary.  This is a statement-level consumer: it
does not construct the dictionary. -/
theorem TripodalDictionary.relations {d : ℕ} (T : TripodalDictionary (K := K) d) :
    (∀ lam, T.logDiff lam = Real.log (T.dFtpd lam)) ∧
    (∀ lam, Real.log (T.fFtpd lam) ≤ Mzk1ULPointConductorActual.pointND (K := K) lam) ∧
    T.dmod ≤ d ∧
    (∀ lam, T.eStar lam ≤ T.Cd) :=
  ⟨T.logDiff_eq, T.fFtpd_le_conductor, T.dmod_le, T.eStar_le⟩

/-- The tripodal dictionary also gives the conductor comparison used by the
D4 estimate after the dictionary is instantiated. -/
theorem TripodalDictionary.fFtpd_conductor_le {d : ℕ} (T : TripodalDictionary (K := K) d)
    (lam : K) : Real.log (T.fFtpd lam) ≤ Mzk1ULPointConductorActual.pointND (K := K) lam :=
  T.fFtpd_le_conductor lam

#print axioms TripodalDictionary.relations
#print axioms TripodalDictionary.fFtpd_conductor_le

end LeanFormal.IUT.XiFPaper.G1D2InterfaceActual
end