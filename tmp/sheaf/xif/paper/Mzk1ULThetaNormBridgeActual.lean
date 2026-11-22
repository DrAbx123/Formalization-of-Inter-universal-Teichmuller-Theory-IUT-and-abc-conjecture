/- C2 theta normalization: K-side M-scale bridge bookkeeping (and the F->K gap).

Findings (kurt 2026-11-17): (i) on the K side the lambda-weighted theta root is
DEFINITIONAL: `ksThetaHullLogRoot_lam = sum_b thetaLamWeight_b * ksThetaHullLog_b`;
(ii) the M-scale versions live in `Mzk1URThetaKLambdaMScaledActual` (K side:
`thetaMWeight`, `ksThetaHullLogRoot_lam_M`) and `Mzk1URThetaKMScaledActual` (F side:
`actualQM`, `actualThetaHullLogRootM`, `neg_actualQM_le_thetaM`), each in its own domain;
(iii) there is NO cross F->K equality in the tree: `perBThetaHullLog` uses the F-side
`qVFamTensorPlaces` while `ksThetaHullLog` uses the K-side `ksPlaces`, so an equality
would need a completion transport `(obligation: F_to_K_completion_iso)`.  This file
therefore re-exports the K-side M-scale objects and records the gap explicitly rather
than asserting a cross-domain identity.
-/
import tmp.sheaf.xif.paper.Mzk1URThetaKLambdaMScaledActual
import tmp.sheaf.xif.paper.Mzk1URThetaKMScaledActual
import tmp.sheaf.xif.paper.Mzk1URThetaKSideActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1ULThetaNormBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKLambdaMScaledActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKMScaledActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- K-side M-scale lambda-weighted theta root (re-export for kurt's C2 chain). -/
noncomputable def ksThetaHullLogRoot_lam_M_adapter (D : ThetaMScaleData (T := T)) : ℝ :=
  ksThetaHullLogRoot_lam_M (T := T) D

/-- K-side lambda weight (re-export). -/
noncomputable def thetaMWeight_adapter (D : ThetaMScaleData (T := T))
    (b : Bad (nativePlaceSelection T)) : ℝ :=
  thetaMWeight (T := T) D b

/-- F-side M-scale theta root (re-export; F-side P6/C2 narrative only). -/
noncomputable def actualThetaHullLogRootM_adapter : ℝ :=
  actualThetaHullLogRootM (T := T)

/-- F-side M-scale q magnitude (re-export; F-side P6/C2 narrative only). -/
noncomputable def actualQM_adapter : ℝ := actualQM (T := T)

end LeanFormal.IUT.XiFPaper.Mzk1ULThetaNormBridgeActual
end
