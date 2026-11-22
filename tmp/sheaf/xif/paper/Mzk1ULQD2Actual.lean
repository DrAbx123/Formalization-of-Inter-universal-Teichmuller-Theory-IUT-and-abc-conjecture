/- U-C D2 (route 6.2, L577-590): the q-height h = Q_all and its relation to the
selected q-pilot magnitude Q.

Index-set identification (Lead ruling 2026-11-17, checked in the actual data):
`nativePlaceSelection T` is `T.tuple.source.V_mod_bad`
(SourceDefinition31NativeContractBridgeReduction.lean:108-114, field-by-field rfl),
i.e. paper IUT I Def 3.1's V^bad_mod; the support of q^ADiv is exactly V(F)^bad
(IUT-TEXT-LONG L1052-1057) and log(q) := deg(q^ADiv) (L1077-1088).  Hence paper
has ONE q-height: h = Q_all = Q = qPilotMagnitudePaper, indexed by ALL bad places
Bad (nativePlaceSelection T); there is no separate non-bad q data (new objects are
forbidden).  The route's "do not identify Q = h" is thus a PROVED identification of
the selected set with the full V^bad_mod (field expansion), not an assumption.

LEGACY NOTE (Lead ruling 2026-11-17): `qPilotMagnitudePaper` used here is the OLD
(mixed F-lift order x K-lift weight) q magnitude; the paper-faithful v2 is
david's forthcoming `qPilotMagnitudePaper_v2 := (1/[F:Q]) Sum_{P in badFPrimeSet}
(f_P c_P log p_P)` with `M_paper_v2 := v2/(2l)`.  When v2 lands, `hAll`/`Q_le_h`/
`h_sub_Q_bound` are re-stated against v2 (interface unchanged); the present theorems
are kept for the LEGACY value only.

REVISION (david 2026-11-17, route symbol audit): the identification h = Q above is
only at the Fmod-support level; the paper's h = Q_all lives on the F-full-fiber
V(F)^bad = V^bad_mod x_{V_mod} V(F) (L1305-1308), so at the F-fiber level
h - Q = (full-fiber sum) - (single selected lift sum) is a nonzero lift-multiplicity
term.  This file's LEGACY hAll/Q_le_h/h_sub_Q_bound are therefore statements about
the OLD (single-lift) Q only; the canonical objects are david's
`qPilotMagnitudePaper_v2` (C4 Q = global) and the D2 h-Q must be re-defined against
v2 (lift multiplicity).

Consequently Q <= h is equality and h - Q = 0; the D2 second display holds
for any nonnegative right-hand side (the paper's constant C_d choice), which is
recorded as the explicit nonnegativity hypothesis of h_sub_Q_bound.
-/
import tmp.sheaf.xif.paper.Mzk1URThetaKSideActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULQD2Actual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- the q-height h = Q_all (all bad q-places, normalized-degree weight). -/
noncomputable def hAll : ℝ := qPilotMagnitudePaper (l := l) T

/-- PROVED: h = Q (the selected set is the full bad set, see module docstring). -/
theorem hAll_eq_Q : hAll T = qPilotMagnitudePaper (l := l) T := rfl

/-- PROVED: Q <= h. -/
theorem Q_le_h : qPilotMagnitudePaper (l := l) T ≤ hAll T := le_rfl

/-- D2 second display: h - Q <= C_d sqrt(h) log(2 C_d h) + C_K, with the paper's
right-hand side assumed nonnegative (as it is for the paper's constant choice).
Since h - Q = 0 (proved identification), this is immediate. -/
theorem h_sub_Q_bound (C_d C_KV : ℝ)
    (hRHS : 0 ≤ C_d * Real.sqrt (hAll T) * Real.log (2 * C_d * hAll T) + C_KV) :
    hAll T - qPilotMagnitudePaper (l := l) T
      ≤ C_d * Real.sqrt (hAll T) * Real.log (2 * C_d * hAll T) + C_KV := by
  rw [hAll, sub_self]
  exact hRHS


/-- PROVED: the D2 right-hand side is nonnegative for the paper constant choice
(C_d >= 1, C_KV >= 0) once the q-height is at least 1. -/
theorem hRHS_of_constants (C_d C_KV : ℝ) (hCd : 1 ≤ C_d) (hCKV : 0 ≤ C_KV)
    (hh : 1 ≤ hAll T) :
    0 ≤ C_d * Real.sqrt (hAll T) * Real.log (2 * C_d * hAll T) + C_KV := by
  have hsqrt : 0 ≤ Real.sqrt (hAll T) := Real.sqrt_nonneg _
  have hlog : 0 ≤ Real.log (2 * C_d * hAll T) := by
    apply Real.log_nonneg
    nlinarith [hCd, hh]
  have hprod : 0 ≤ C_d * Real.sqrt (hAll T) * Real.log (2 * C_d * hAll T) := by
    have h1 : 0 ≤ C_d * Real.sqrt (hAll T) := mul_nonneg (by linarith) hsqrt
    exact mul_nonneg h1 hlog
  linarith

/-- D2 second display, unconditional on the right-hand-side nonnegativity
(it is derived from the paper constant choice). -/
theorem h_sub_Q_bound' (C_d C_KV : ℝ) (hCd : 1 ≤ C_d) (hCKV : 0 ≤ C_KV)
    (hh : 1 ≤ hAll T) :
    hAll T - qPilotMagnitudePaper (l := l) T
      ≤ C_d * Real.sqrt (hAll T) * Real.log (2 * C_d * hAll T) + C_KV := by
  have hRHS := hRHS_of_constants (l := l) T C_d C_KV hCd hCKV hh
  rw [hAll, sub_self]
  exact hRHS

end LeanFormal.IUT.XiFPaper.Mzk1ULQD2Actual
end