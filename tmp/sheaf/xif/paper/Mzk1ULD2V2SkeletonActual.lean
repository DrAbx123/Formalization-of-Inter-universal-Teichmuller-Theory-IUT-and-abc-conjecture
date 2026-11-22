/- U-C D2 (route 6.2 L577-590): h = Q_all vs Q, paper-faithful v2 skeleton.

INTERMEDIATE INTERFACE ONLY (Lead ruling 2026-11-17): `hAllV2` is defined as
David's paper-faithful full-fiber q magnitude `qPilotMagnitudePaper_v2`; `Q` is the
LEGACY single-lift `qPilotMagnitudePaper`.  Their difference is the lift-multiplicity
term, and the D2 second bound is expressed through two explicit data interfaces:
  * `PerPrimeLiftData`  -- per-prime relation c_P (F-fiber) vs c_b (single lift),
    fiber counting and Sum e f; TO BE DISCHARGED by david's per-prime data;
  * `PrimeCutoffData`   -- the C_d sqrt(h) log(2 C_d h) + C_{K_V} cutoff estimate
    (Section2 Chebyshev donors); TO BE DISCHARGED by the Section2/P8 donors.
The theorem `d2SecondForm_of_data` is only an assembly: it does NOT claim the D2
inequalities are proved, and the final L-H version must instantiate these two
interfaces (docstring requirement).
-/
import tmp.sheaf.xif.paper.Mzk1ULQPilotMagnitudeV2Actual
import tmp.sheaf.xif.paper.Mzk1URThetaKSideActual
import tmp.sheaf.xif.paper.Mzk1ULD2SecondFormActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULD2V2SkeletonActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual
open LeanFormal.IUT.XiFPaper.Mzk1ULD2SecondFormActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/- SCALE NOTE (audit Q-NORMALIZATION): hAllV2 is the Q-slot object (paper Q_all, 1/[F:Q], f-family, NO 1/(2l)); the C2/hP5 M-slot is M = Q/(2l) = M_paper_v2 (paper |log q| = (1/2l) log q, IUT IV L1359-1364).  QSingle below is the LEGACY gamma-family reference only (single F lift, K/F mixed weight), not paper Q. -/

/-- h := Q_all for the paper-faithful (full F-fiber) q magnitude. -/
noncomputable def hAllV2 : ℝ := qPilotMagnitudePaper_v2 (l := l) T

/-- PROVED (definitional): hAllV2 is the full-fiber q magnitude. -/
theorem hAllV2_eq : hAllV2 T = qPilotMagnitudePaper_v2 (l := l) T := rfl

/-- Q := the LEGACY single-lift q magnitude (retained for the difference term). -/
noncomputable def QSingle : ℝ := qPilotMagnitudePaper (l := l) T

/-- PROVED: hAllV2 is nonnegative (David's zero_le_qPilotMagnitudePaper_v2). -/
theorem hAllV2_nonneg : 0 ≤ hAllV2 T :=
  zero_le_qPilotMagnitudePaper_v2 (l := l) T

/-- INTERMEDIATE per-prime lift data: the difference decomposition (to be
discharged by David's per-prime c_P vs c_b / fiber counting / Sum e f). -/
structure PerPrimeLiftData where
  diff : ℝ
  h_diff : diff = hAllV2 T - QSingle T
  h_diff_nonneg : 0 ≤ diff

/-- INTERMEDIATE cutoff data: the D2 second-display right-hand side (to be
discharged by Section2 Chebyshev/P8 donors). -/
structure PrimeCutoffData (D : PerPrimeLiftData T) where
  Cd : ℝ
  CKV : ℝ
  hCd : 0 ≤ Cd
  h_bound : D.diff ≤ Cd * Real.sqrt (hAllV2 T) * Real.log (2 * Cd * hAllV2 T) + CKV

/-- ASSEMBLY: from the two intermediate data interfaces, produce the D2 second
form for the paper-faithful objects (INTERMEDIATE; not a proof of D2). -/
noncomputable def d2SecondForm_of_data (D : PerPrimeLiftData T)
    (C : PrimeCutoffData T D) : D2SecondForm where
  h := hAllV2 T
  Q := QSingle T
  Cd := C.Cd
  CKV := C.CKV
  h_nonneg := hAllV2_nonneg T
  Cd_nonneg := C.hCd
  h_sub_Q_nonneg := D.h_diff.symm ▸ D.h_diff_nonneg
  h_sub_Q_le := D.h_diff.symm ▸ C.h_bound

end LeanFormal.IUT.XiFPaper.Mzk1ULD2V2SkeletonActual
end
