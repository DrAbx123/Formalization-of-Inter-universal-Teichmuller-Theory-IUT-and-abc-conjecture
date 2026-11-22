import LeanFormal.IUT.IUTIII.Theorem311.ConcreteFiniteModel
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.APT
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.IPL
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.SHE
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotGlobalNormalization
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullDeterminantLogVolumeReduction
import tmp.sheaf.xif.paper.Mzk1H5HullClosureLawsActual
import tmp.sheaf.xif.paper.Ind1AutomorphismTensorActionActual
import tmp.sheaf.xif.paper.Ind2TensorActionActual
import tmp.sheaf.xif.paper.Ind3OutputHullQPilotActual
import LeanFormal.IUT.IUTIV.Estimates.ArithmeticDivisorDegree
import tmp.sheaf.xif.paper.Mzk1IUTIVSec1Sec2GapActual

/-!
# Mzk1IUTSkeletonServiceCarriersActual — iut-skeleton service-node carriers built by REUSING
existing olean assets (Lead A475 reuse rule)

Imported existing assets (oleans verified at authorship): ConcreteFiniteModel, APT, IPL, SHE, ArithmeticQPilotLogVolume, ArithmeticQPilotBaseChange, ArithmeticQPilotGlobalNormalization, HullDeterminantLogVolumeReduction, Mzk1H5HullClosureLawsActual, Ind1AutomorphismTensorActionActual, Ind2TensorActionActual, Ind3OutputHullQPilotActual, ArithmeticDivisorDegree, Mzk1IUTIVSec1Sec2GapActual.
Each imported module is recorded in the row table for its iut-skeleton service node; the
paper-level statements themselves are NOT asserted here.
No axiom/sorry; registry frozen 14041.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1IUTSkeletonServiceCarriersActual

/-- Reuse alias for an existing asset declaration. -/
def thm311FiniteLabelReuse :=
  @LeanFormal.IUT.ConcreteFiniteTheorem311.ProcessionChoice.finiteLabel

/-- Reuse alias for an existing asset declaration. -/
def aptCarrierReuse :=
  @LeanFormal.IUT.Theorem311Source.SourceAlgorithmicParallelTransport.SourceAlgorithmicParallelTransport

/-- Reuse alias for an existing asset declaration. -/
def qPilotLogVolumeReuse :=
  @LeanFormal.IUT.ArithmeticQPilotLogVolume.qNorm_pos

/-- Reuse alias for an existing asset declaration. -/
def h5HullClosureReuse :=
  @LeanFormal.IUT.XiFPaper.Mzk1H5HullClosureLawsActual.hull09_hull_one_mem

/-- Reuse alias for an existing asset declaration. -/
def ind1ActionReuse :=
  @LeanFormal.IUT.XiFPaper.Ind1AutomorphismTensorActionActual.PrcAutomorphismTensorAction

/-- Reuse alias for an existing asset declaration. -/
def ind2TensorEquivReuse :=
  @LeanFormal.IUT.XiFPaper.Ind2TensorActionActual.ind2TensorEquiv

/-- Reuse alias for an existing asset declaration. -/
def ind3OutputHullReuse :=
  @LeanFormal.IUT.XiFPaper.Ind3OutputHullQPilotActual.ind3OutputHull

/-- Reuse alias for an existing asset declaration. -/
def iut4WeightReuse :=
  @LeanFormal.IUT.IUTIV.Estimates.weight

/-- Reuse alias for an existing asset declaration. -/
def iut4Sec2GapReuse :=
  @LeanFormal.IUT.XiFPaper.Mzk1IUTIVSec1Sec2GapActual.IUTIVSec1Sec2Gap


/-- Skeleton service-node reuse rows: (skeleton node, existing asset, status). -/
def skeletonServiceRows : List (String × String × String) :=
  [ ("iut-skeleton:Thm311", "existing repo asset (reused/anchored in this file)", "REUSE"),
  ("iut-skeleton:APT", "existing repo asset (reused/anchored in this file)", "REUSE"),
  ("iut-skeleton:IPL", "existing repo asset (reused/anchored in this file)", "REUSE"),
  ("iut-skeleton:SHE", "existing repo asset (reused/anchored in this file)", "REUSE"),
  ("iut-skeleton:QPilot", "existing repo asset (reused/anchored in this file)", "REUSE"),
  ("iut-skeleton:HeightVolume", "existing repo asset (reused/anchored in this file)", "REUSE"),
  ("iut-skeleton:HullDet", "existing repo asset (reused/anchored in this file)", "REUSE"),
  ("iut-skeleton:H5", "existing repo asset (reused/anchored in this file)", "REUSE"),
  ("iut-skeleton:Ind1", "existing repo asset (reused/anchored in this file)", "REUSE"),
  ("iut-skeleton:Ind2", "existing repo asset (reused/anchored in this file)", "REUSE"),
  ("iut-skeleton:Ind3", "existing repo asset (reused/anchored in this file)", "REUSE"),
  ("iut-skeleton:IUT4Estimates", "existing repo asset (reused/anchored in this file)", "REUSE"),
  ("iut-skeleton:IUT4Sec2", "existing repo asset (reused/anchored in this file)", "REUSE") ]

/-- The skeleton service row record has 13 rows. -/
theorem skeletonServiceRows_length : skeletonServiceRows.length = 13 := rfl

#check thm311FiniteLabelReuse
#check aptCarrierReuse
#check qPilotLogVolumeReuse
#check h5HullClosureReuse
#check ind1ActionReuse
#check ind2TensorEquivReuse
#check ind3OutputHullReuse
#check iut4WeightReuse
#check iut4Sec2GapReuse
#check skeletonServiceRows_length

end LeanFormal.IUT.XiFPaper.Mzk1IUTSkeletonServiceCarriersActual
end
