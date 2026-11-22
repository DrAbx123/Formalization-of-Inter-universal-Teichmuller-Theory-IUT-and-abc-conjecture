import tmp.sheaf.xif.paper.S3133S3131GaussianModelMapMinimalActual
import LeanFormal.IUT.Audit.Status

/-!
# S3137: light R1 reduced-residual consumer (qpilot minimal Gaussian model map)

OPS split per Lead: the heavy readout/instance route is kept out of this file.
This light consumer only imports qpilot's S3133GaussianModelMapMinimalActual and
records the reduced R1 residual where M0 and M3 are PROVED from qpilot's
actual theorems and M1 + shrunk M2 are the genuine remaining residual
propositions.  The readout side (M4/M5) and the comparison are handled in the
already-green S3137SameCModelMapResidualActual / S3137QThetaComparisonBridgeActual
files, which do not depend on the qpilot/S1280 route.

qpilot status (confirmed): S3137R1_interface : M0 ∧ M3 ∧ ((m1 ∧ m2) ↔ Remaining);
M0 = S3133GaussianModelMapResidualMinimal_m0; M3 = ..._m3.
No assertion of residual fields, no carrier substitution, no sorry, no axiom.
WRITE-ONLY.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3137GaussianR1ResidualLightActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3GaussianThetaPacketActual
open LeanFormal.IUT.XiFPaper.S3133S3131GaussianModelComponentsActual
open LeanFormal.IUT.XiFPaper.S3133S3131GaussianModelMapMinimalActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (D : SourcePilotRegionDonors (I := I))
variable (R : S3133GaussianModelMapResidualMinimal (l := l) (I := I) D)

/-- **Reduced R1 residual (light form).**  M0 and M3 are PROVED fields filled
from qpilot's actual theorems; M1 and shrunk M2 are the genuine remaining
residual propositions (source placeToMod provenance; clause-B base-q descent). -/
structure GaussianR1ReducedResidual : Prop where
  /-- M0 PROVED: actual SourceCompletion above the concrete Gaussian arithmetic -/
  m0 : S3133GaussianModelArithmeticMatch (l := l) R.C.toSourceNativeInitialThetaData
  /-- M1 residual: bad <-> all-place index injection (source placeToMod missing) -/
  m1 : R.m1_indexInjection
  /-- M2 residual: clause-B base-q descent with Gaussian norm 1/5 above 5 -/
  m2 : R.m2_baseQMatch
  /-- M3 PROVED: actual Gaussian Stage-2 theta values match the source theater -/
  m3 : S3133GaussianThetaValueMatch (l := l) (V := V) (I := I)
    (actualGaussianC3 (l := l) (V := V) (I := I) D)

/-- **Construct the reduced R1 residual**: M0/M3 proved from qpilot; only M1
and M2 are assumed. -/
theorem gaussianR1ReducedResidual_of_qpilot
    (hM1 : R.m1_indexInjection) (hM2 : R.m2_baseQMatch) :
    GaussianR1ReducedResidual (l := l) (V := V) (I := I) D R where
  m0 := S3133GaussianModelMapResidualMinimal_m0 (l := l) (V := V) (I := I) D R
  m1 := hM1
  m2 := hM2
  m3 := S3133GaussianModelMapResidualMinimal_m3 (l := l) (V := V) (I := I) D

/-- **Exact residual identification**: the reduced R1 residual is equivalent to
exactly M1 and shrunk M2, the two genuine missing fields. -/
theorem gaussianR1ReducedResidual_residual_iff :
    GaussianR1ReducedResidual (l := l) (V := V) (I := I) D R ↔
      (R.m1_indexInjection ∧ R.m2_baseQMatch) := by
  constructor
  · intro M
    exact ⟨M.m1, M.m2⟩
  · rintro ⟨h1, h2⟩
    exact gaussianR1ReducedResidual_of_qpilot (l := l) (V := V) (I := I) D R h1 h2

/-- **M0 + M3 bundle** as PROVED actual theorems for the Gaussian model (the
part of R1 that is no longer residual). -/
theorem gaussianR1_M0_M3_proved :
    S3133GaussianModelArithmeticMatch (l := l) R.C.toSourceNativeInitialThetaData ∧
      S3133GaussianThetaValueMatch (l := l) (V := V) (I := I)
        (actualGaussianC3 (l := l) (V := V) (I := I) D) :=
  ⟨S3133GaussianModelMapResidualMinimal_m0 (l := l) (V := V) (I := I) D R,
    S3133GaussianModelMapResidualMinimal_m3 (l := l) (V := V) (I := I) D⟩

end LeanFormal.IUT.XiFPaper.S3137GaussianR1ResidualLightActual

namespace LeanFormal.IUT.Audit

/-- **Light R1 reduced residual status.**  M0 PROVED (actual SourceCompletion
with model arithmetic) and M3 PROVED (actual Gaussian Stage-2 theta values vs
source theater) via qpilot S3133GaussianModelMapResidualMinimal_m0/_m3.
Reduced residual is exactly M1 (source placeToMod provenance; bad<->all-place
index injection, contract-separated missing) + shrunk M2 (clause-B base-q
descent, Gaussian norm 1/5 above 5).  Readout side M4/M5 and the Cor 3.12
comparison live in the green S3137 model-map residual / bridge files and do not
depend on this heavy route. -/
def s3137GaussianR1ReducedLight : Obligation :=
  { id := "S3137.residual.R1-light-reduced"
    source := "IUT I, Def 3.1, Ex. 3.2(iv); IUT II, Remark 2.5.1, (i); IUT III, Prop. 3.4, (ii), pp. 102-103; Def. 3.8, (i), p. 112"
    status := VerificationStatus.pending
    note := "M0/M3 proved via qpilot; residual exactly M1 (source placeToMod provenance) + shrunk M2 (clause-B base-q descent/Gaussian norm).  Readout/comparison in green S3137 files.  No residual proof assumed."
    dependsOn := ["S3133S3131GaussianModelMapMinimalActual", "S3137GaussianR1ResidualLightActual"] }

end LeanFormal.IUT.Audit