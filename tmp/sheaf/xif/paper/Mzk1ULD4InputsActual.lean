/- U-C D4 input assembly (route 6.4, L613-638): the consumption shape for
the independent IV bound -> D1 absorption.

route 6.4 lists the tripodal-dictionary relations used by Cor 2.2:
  log-diff_X(lam)=log d_Ftpd; log f_Ftpd <= N_D(lam); d_mod <= d; e* controlled;
and the final display / C5 branch feed D4 (route L623-632).  This file fixes the
INPUT PACKAGE (`D4Inputs`) consumed by D4: the actual Q/M letters (paper-faithful
v2/ M_paper_v2), S_ar (paper-faithful SAr_tripodal), and the still-open letter
obligations hlogK / hsQ / hcond (with their actual-object statements), plus the
D2 second-form data.  The fields are the ACTUAL obligations to be discharged
(david QSelected/per-prime, Legendre/support, Section2); this file claims no
inequality itself.
-/
import tmp.sheaf.xif.paper.Mzk1ULQPilotMagnitudeV2Actual
import tmp.sheaf.xif.paper.Mzk1ULPaperLettersActual
import tmp.sheaf.xif.paper.Mzk1ULKSideLettersActual
import tmp.sheaf.xif.paper.Mzk1ULD2SecondFormActual
import tmp.sheaf.xif.paper.Mzk1URThetaKSideActual
import tmp.sheaf.xif.paper.Mzk1ULSQPaperActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULD4InputsActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual
open LeanFormal.IUT.XiFPaper.Mzk1ULPaperLettersActual
open LeanFormal.IUT.XiFPaper.Mzk1ULD2SecondFormActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual
open LeanFormal.IUT.XiFPaper.Mzk1ULSQPaperActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- D4 input package (route 6.4): actual Q/M letters, S_ar, the D2 second form,
and the three open letter obligations in their actual-object form. -/
structure D4Inputs where
  /-- Q: paper-faithful full-fiber q magnitude (D2/degree side). -/
  Q : ℝ
  Q_eq : Q = qPilotMagnitudePaper_v2 (l := l) T
  /-- M = Q/(2l) (paper |log q|). -/
  M : ℝ
  M_eq : M = M_paper_v2 (l := l) T
  /-- d_mod: the degree (dMod T). -/
  dMod : ℝ
  /-- S_ar: paper-faithful (log d_F + place-weighted log f_F). -/
  S_ar : ℝ
  S_ar_eq : S_ar = SAr_tripodal T
  /-- paper Step (ii) letter obligation (route L615, paper L1424). -/
  hlogK : Real.log (NumberField.rootDiscr T.arithmetic.K) ≤ S_ar + 2 * Real.log (l.value : ℝ) + 21
  /-- paper Step (iii)/s^Q letter obligation (route L615, paper L1572). -/
  hsQ : Real.log (sQPaper T) ≤ 2 * dMod * S_ar + 5 + Real.log (l.value : ℝ)
  /-- D2 second form (h = Q_all vs Q relation). -/
  d2 : D2SecondForm

/-- PROVED: Q of the D4 package is the paper-faithful full-fiber q magnitude. -/
theorem D4Inputs.Q_is_v2 (D : D4Inputs T) : D.Q = qPilotMagnitudePaper_v2 (l := l) T :=
  D.Q_eq

/-- PROVED: M of the D4 package is M_paper_v2. -/
theorem D4Inputs.M_is_MpaperV2 (D : D4Inputs T) : D.M = M_paper_v2 (l := l) T :=
  D.M_eq

/-- PROVED: S_ar of the D4 package is SAr_tripodal. -/
theorem D4Inputs.S_ar_is_tripodal (D : D4Inputs T) : D.S_ar = SAr_tripodal T :=
  D.S_ar_eq

end LeanFormal.IUT.XiFPaper.Mzk1ULD4InputsActual
end