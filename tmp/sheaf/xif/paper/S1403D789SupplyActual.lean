import tmp.sheaf.xif.paper.S1386D7bLocalGroupActual
import tmp.sheaf.xif.paper.S1387D9PaperSlotActual
import tmp.sheaf.xif.paper.S1383RealCuspCoordinateActual
import tmp.sheaf.xif.paper.S1312D7LocalGroupActual
import tmp.sheaf.xif.paper.S1330CuspEpsilonActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31D4D9Supply

/-! # S1403: conditional D7/D8/D9 supply assembly

Inputs are the exact objects only:

* D7b: D7LocalGroupSectionSupply over the actual canonical D7a layer
  (S1312/S1386 exact first field).
* D8: SourceSignQuotientData + S1330RealCuspCoordinate (S1383 exact first
  field); the actual cusp clause is produced by the existing
  S1330CuspClauseOfRealCuspCoordinate, using the actual paper cusp
  S1330PaperEpsilon.
* D9: S1360D9OrbicurveSlot (S1387 paper slot exact first field + remainder +
  K-core).

The actual sections clause is produced by the existing d7SectionLayerBridge.
No terminal/point-fiber/arithmetic G_v substitute is used.  The D4/D5/D6
inputs are not invented here; the assembly is conditional on them in the
eventual D4D9Supply consumer. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1403D789SupplyActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.Definition31D4D9Supply
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1312D7LocalGroupActual
open LeanFormal.IUT.XiFPaper.S1330CuspEpsilonActual
open LeanFormal.IUT.XiFPaper.S1360D9OrbicurveSlotActual
open LeanFormal.IUT.XiFPaper.S1386D7bLocalGroupActual
open LeanFormal.IUT.XiFPaper.S1387D9PaperSlotActual
open LeanFormal.IUT.XiFPaper.S1383RealCuspCoordinateActual

/-- Conditional D7/D8/D9 bundle using only the exact source objects. -/
structure S1403D789ConditionalSupply (l : PrimeGeFive) where
  /-- D7b exact supply over the actual canonical D7a layer. -/
  d7b : D7LocalGroupSectionSupply.{0, 0} (S1312D7Layer l)
  /-- Sign-quotient data needed by the D8 cusp coordinate. -/
  signData : SourceSignQuotientData (S1280Arithmetic l)
  /-- D8 exact real cusp coordinate. -/
  d8 : S1330RealCuspCoordinate l signData
  /-- D9 paper orbicurve slot (first field + remainder + K-core). -/
  d9 : S1360D9OrbicurveSlot l

/-- Actual D7 sections clause from the D7b supply. -/
noncomputable def S1403Sections (l : PrimeGeFive)
    (X : S1403D789ConditionalSupply l) : SourceSectionClause.{0, 0, 0} :=
  d7SectionLayerBridge (S1312D7Layer l) X.d7b

/-- Actual D8 cusp clause from the real cusp coordinate and the actual paper
cusp. -/
noncomputable def S1403Cusp (l : PrimeGeFive)
    (X : S1403D789ConditionalSupply l) : SourceCuspClause :=
  S1330CuspClauseOfRealCuspCoordinate X.d8 (S1330PaperEpsilon l X.signData)

/-- Actual D9 orbicurve slot projection. -/
noncomputable def S1403D9Slot (l : PrimeGeFive)
    (X : S1403D789ConditionalSupply l) : S1360D9OrbicurveSlot l :=
  X.d9

/-- D7 section clause is definitionally the d7SectionLayerBridge of the D7b
supply; no extra section data was invented. -/
@[simp] theorem S1403Sections_eq (l : PrimeGeFive)
    (X : S1403D789ConditionalSupply l) :
    S1403Sections l X = d7SectionLayerBridge (S1312D7Layer l) X.d7b := rfl

/-- D8 cusp epsilon is the supplied real epsilon of the chosen paper cusp. -/
@[simp] theorem S1403Cusp_epsilon (l : PrimeGeFive)
    (X : S1403D789ConditionalSupply l) :
    (S1403Cusp l X).epsilon = X.d8.epsilonOf (S1330PaperEpsilon l X.signData) :=
  rfl

/-- The conditional bundle projects the D9 slot unchanged. -/
@[simp] theorem S1403D9Slot_eq (l : PrimeGeFive)
    (X : S1403D789ConditionalSupply l) :
    S1403D9Slot l X = X.d9 := rfl

end LeanFormal.IUT.XiFPaper.S1403D789SupplyActual
end