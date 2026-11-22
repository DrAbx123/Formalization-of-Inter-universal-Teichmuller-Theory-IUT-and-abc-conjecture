import tmp.sheaf.xif.paper.Mzk1Example36EtThCorrespondenceActual
import LeanFormal.IUT.Foundations.Theta.GaussianKernel
import LeanFormal.IUT.IUTII.Theta.EtaleThetaQuotient
import LeanFormal.IUT.IUTI.InitialTheta.SourceInitialThetaData
import LeanFormal.IUT.IUTI.HodgeTheater.ConcreteHodgeTheaterExample
import LeanFormal.IUT.IUTII.Theta.ConcreteSourceEtaleThetaBridge

/-!
# Mzk1AbsoluteThetaDataCarrierActualAdapted (adapted copy, A475 reuse) — carrier for the paper's absolute theta data
(Θ-pilot / absolute theta function data), asset-first

STEP 0 prior-art used here (all existing assets, no new mathematics):
* Example36 analytic theta side: AnalyticThetaCarrier/analyticThetaQExpansion/
  analyticThetaCarrierConcrete/gaussianFiveThetaQ and the Example36<->EtTh correspondence
  bundle (Mzk1Example36EtThCorrespondenceActual);
* Foundations/Theta Gaussian kernel realThetaValue (Gaussian theta values);
* IUTI Initial Theta data (SourceInitialThetaData) and the concrete Gaussian Hodge theater
  example (ConcreteHodgeTheaterExample);
* IUTII concrete source etale theta bridge (cStage/packet/etc. as an imported asset layer).

WHAT THIS FILE DOES:
* defines the typed carrier for the absolute theta data used by the theta-pilot: analytic
  theta carrier + Example36<->EtTh correspondence bundle, with the Gaussian theta values
  definitionally linked to the analytic q-expansion;
* inhabits it for every prime l >= 5 from the tree assets;
* records the rows and keeps the paper-level absolute theta data construction NAMED (the
  carrier is transport, not the paper's construction/proof).
No axiom/sorry; registry frozen 14041.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1AbsoluteThetaDataCarrierActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceThetaGenerator
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceThetaDivisor
open LeanFormal.IUT.IUTII.Frobenioid.Example36.ThetaSeries
open LeanFormal.IUT.XiFPaper.Mzk1Example36EtThCorrespondenceActual

/-- The carrier for the paper's absolute theta data: the analytic theta carrier together
with the Example36 <-> EtTh correspondence bundle. -/
structure AbsoluteThetaDataCarrier (l : PrimeGeFive) where
  /-- the real analytic theta carrier (q-parameter 0 < q < 1). -/
  thetaCarrier : AnalyticThetaCarrier
  /-- the Example36 <-> EtTh correspondence bundle (analytic theta + boundary + generator). -/
  correspondence : Example36EtThCorrespondence l

/-- The absolute theta data carrier is inhabited by the tree assets for every l >= 5. -/
noncomputable def absoluteThetaDataCarrier (l : PrimeGeFive) :
    AbsoluteThetaDataCarrier l where
  thetaCarrier := analyticThetaCarrierConcrete
  correspondence := example36EtThCorrespondence l

/-- The absolute theta data carrier is nonempty for every l >= 5. -/
theorem absoluteThetaDataCarrier_nonempty (l : PrimeGeFive) :
    Nonempty (AbsoluteThetaDataCarrier l) :=
  ⟨absoluteThetaDataCarrier l⟩

/-- The carrier's Gaussian theta values are definitionally the analytic q-expansion of the
carried theta carrier. -/
theorem absoluteThetaData_gaussian_eq_qExpansion {l : PrimeGeFive} (A : AbsoluteThetaDataCarrier l) (n : ℤ) :
    realThetaValue A.thetaCarrier.q n = analyticThetaQExpansion A.thetaCarrier n := rfl

/-- The concrete carried q-parameter is the Example36 value gaussianFiveThetaQ. -/
theorem absoluteThetaDataCarrier_concrete_q (l : PrimeGeFive) :
    (absoluteThetaDataCarrier l).thetaCarrier.q = gaussianFiveThetaQ := rfl

/-- The concrete carried q-parameter lies in the convergence range (0,1). -/
theorem absoluteThetaDataCarrier_concrete_q_mem (l : PrimeGeFive) :
    0 < (absoluteThetaDataCarrier l).thetaCarrier.q ∧
      (absoluteThetaDataCarrier l).thetaCarrier.q < 1 :=
  ⟨(absoluteThetaDataCarrier l).thetaCarrier.q_pos,
    (absoluteThetaDataCarrier l).thetaCarrier.q_lt_one⟩

/-- Carrier rows: (paper object, formal carrier/asset, status). -/
def absoluteThetaDataRows : List (String × String × String) :=
  [ ("analytic theta carrier (q-parameter 0<q<1)", "AnalyticThetaCarrier; analyticThetaCarrierConcrete (gaussianFiveThetaQ)", "CARRIER (tree asset)"),
    ("Gaussian theta values", "realThetaValue; absoluteThetaData_gaussian_eq_qExpansion", "PROVED (rfl)"),
    ("Example36<->EtTh correspondence bundle", "Example36EtThCorrespondence; example36EtThCorrespondence", "CARRIER (X1, EXIT0/CITABLE)"),
    ("Initial Theta data / concrete c-stage", "SourceInitialThetaData; ConcreteSourceEtaleThetaBridge.cStage", "TREE ASSET (imported)"),
    ("Gaussian Hodge theater example", "gaussianHodgeTheater (ConcreteHodgeTheaterExample)", "TREE ASSET (imported)"),
    ("paper absolute theta data construction (Θ-pilot data)", "not asserted: carrier only; construction/proof remains a paper input", "NAMED") ]

/-- The carrier row record has six rows. -/
theorem absoluteThetaDataRows_length : absoluteThetaDataRows.length = 6 := rfl

#check AbsoluteThetaDataCarrier
#check absoluteThetaDataCarrier
#check absoluteThetaDataCarrier_nonempty
#check absoluteThetaData_gaussian_eq_qExpansion
#check absoluteThetaDataCarrier_concrete_q_mem
#check absoluteThetaDataRows_length

end LeanFormal.IUT.XiFPaper.Mzk1AbsoluteThetaDataCarrierActualAdapted
end
