import tmp.sheaf.xif.paper.PaperC3TensorBlockActual
import tmp.sheaf.xif.paper.RootHullContainmentInequalityActual
import tmp.sheaf.xif.paper.SignedLabelOneActual

/-!
# Generic qPilot region on the source-geometry block

The qVFamTensorBlock and the generic Block are different carriers.  This file
avoids that mismatch: it defines the qPilot classical region directly on the
generic Block using the actual G.qUnit.

  genericQPilotCoefficient v = -log ||qUnit v|| / log p,
  genericQPilotRegion = qPilotClassicalRegion G.places G.tuple
                          genericQPilotCoefficient.

The actual qPilot image point qUnit is proved to lie in qParameterUnitLambdaHull.
The entire qPilot region -> qUnitLambdaHull inclusion is recorded as an exact
error/unit-correction gap, not assumed.
-/

noncomputable section
open scoped BigOperators Pointwise
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.GenericQPilotCompletionPowerActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3TensorBlockActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual

universe u v

variable {l : PrimeGeFive}
variable {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {V : Type} [Fintype V]
variable (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)

/-- The actual qUnit norm coefficient, the generic qVFamily correction scalar. -/
noncomputable def genericQPilotCoefficient (v : V) : Real :=
  - Real.log ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ /
      Real.log (p : Real)

/-- The actual qPilot classical region on the generic Block. -/
noncomputable def genericQPilotRegion : Set (Block (G := G)) :=
  qPilotClassicalRegion (fun v (_ : Unit) => G.place v) (fun _ => ())
    (genericQPilotCoefficient (G := G))

/-- The actual qPilot image point (label 1 qUnit power). -/
noncomputable def genericQPilotImagePoint : Block (G := G) :=
  paperQParameterImagePoint (G := G) (l := l) (oneLabel l)

/-- The qPilot image point actually lies in the qUnit lambda-O hull. -/
theorem genericQPilotImagePoint_mem_qUnitLambdaHull
    (hq : ∀ v : V,
      ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≤ 1) :
    genericQPilotImagePoint (G := G) ∈
      qParameterUnitLambdaHull (G := G) := by
  have hmem : paperQParameterImagePoint (G := G) (l := l) (oneLabel l) ∈
      paperQParameterNonzeroImageSet (G := G) (l := l) :=
    ⟨oneLabel l, by rw [gaussExponent_oneLabel], rfl⟩
  simpa [genericQPilotImagePoint, qParameterUnitLambdaHull, paperQUnitLambdaHull] using
    paperQParameterNonzeroImageSet_subset_qParameterUnitLambdaRegion
      (G := G) (l := l) hq hmem

/-- Exact qPilot region/completion hull gap.  Only the image point containment
is proved; the full region inclusion needs the qUnit unit part and the
fractional-lattice coefficient normalization. -/
structure GenericQPilotRegionQUnitHullGap where
  region : Set (Block (G := G))
  region_eq : region = genericQPilotRegion (G := G)
  imagePoint : Block (G := G)
  imagePoint_eq : imagePoint = genericQPilotImagePoint (G := G)
  completionHull : Set (Block (G := G))
  completionHull_eq : completionHull = qParameterUnitLambdaHull (G := G)
  imagePoint_mem_completionHull : imagePoint ∈ completionHull
  region_subset_completionHull : Prop
  unitCorrection : Prop
  coefficientNormalization : Prop

/-- Actual partial image data: the qPilot image point lies in the qUnit hull. -/
structure GenericQPilotImageData where
  region : Set (Block (G := G))
  region_eq : region = genericQPilotRegion (G := G)
  imagePoint : Block (G := G)
  imagePoint_eq : imagePoint = genericQPilotImagePoint (G := G)
  completionHull : Set (Block (G := G))
  completionHull_eq : completionHull = qParameterUnitLambdaHull (G := G)
  imagePoint_mem_completionHull : imagePoint ∈ completionHull

/-- Actual image data. -/
noncomputable def genericQPilotImageData
    (hq : ∀ v : V,
      ‖(G.qUnit v : CommonPrimeCompletion (G.place v))‖ ≤ 1) :
    GenericQPilotImageData (G := G) where
  region := genericQPilotRegion (G := G)
  region_eq := rfl
  imagePoint := genericQPilotImagePoint (G := G)
  imagePoint_eq := rfl
  completionHull := qParameterUnitLambdaHull (G := G)
  completionHull_eq := rfl
  imagePoint_mem_completionHull :=
    genericQPilotImagePoint_mem_qUnitLambdaHull (G := G) (l := l) hq

/-- Exact missing full-region inclusion object. -/
structure GenericQPilotRegionSubsetGap where
  region_subset_completionHull : Prop
  unitCorrection_eq : Prop
  coefficientNormalization_eq : Prop

/-- Exact missing object. -/
def GenericQPilotRegionSubsetGapRequired : Prop :=
  Nonempty (GenericQPilotRegionSubsetGap)

/-- Consumer relation: the generic qPilot region is actual, the image point is
actual in the qUnit hull, but the full region inclusion remains exact. -/
def GenericQPilotRegionImageOnly : Prop :=
  GenericQPilotRegionSubsetGapRequired


/-- The actual correction unit is the qUnit tensor unit. -/
noncomputable abbrev genericQPilotCorrectionUnit : (Block (G := G))ˣ :=
  qParameterUnitLambdaUnit (G := G)

/-- The completion qUnit hull is exactly the scaled region of the actual
correction unit. -/
theorem qParameterUnitLambdaHull_eq_scaledRegion_correctionUnit :
    qParameterUnitLambdaHull (G := G) =
      paperScaledRegion (G := G)
        (genericQPilotCorrectionUnit (G := G) : Block (G := G)) := rfl

/-- Actual correction-unit data. -/
structure GenericQPilotCorrectionUnitData where
  unit : (Block (G := G))ˣ
  unit_eq : unit = genericQPilotCorrectionUnit (G := G)
  unitRegion : Set (Block (G := G))
  unitRegion_eq : unitRegion =
    paperScaledRegion (G := G) (unit : Block (G := G))
  unitRegion_eq_hull : unitRegion = qParameterUnitLambdaHull (G := G)

/-- Actual correction-unit data. -/
noncomputable def genericQPilotCorrectionUnitData :
    GenericQPilotCorrectionUnitData (G := G) where
  unit := genericQPilotCorrectionUnit (G := G)
  unit_eq := rfl
  unitRegion := paperScaledRegion (G := G)
    (genericQPilotCorrectionUnit (G := G) : Block (G := G))
  unitRegion_eq := rfl
  unitRegion_eq_hull :=
    (qParameterUnitLambdaHull_eq_scaledRegion_correctionUnit (G := G)).symm

/-- Exact unit-correction gap: qPilot region = F(c)O and qUnit hull =
u O with u the qUnit tensor unit.  Equality/subset requires the actual
unit-integrality and coefficient normalization, not assumed here. -/
structure GenericQPilotRegionUnitCorrectionGap where
  qPilotRegion : Set (Block (G := G))
  qPilotRegion_eq : qPilotRegion = genericQPilotRegion (G := G)
  qUnitHull : Set (Block (G := G))
  qUnitHull_eq : qUnitHull = qParameterUnitLambdaHull (G := G)
  correctionUnit : (Block (G := G))ˣ
  correctionUnit_eq : correctionUnit = genericQPilotCorrectionUnit (G := G)
  qPilotRegion_subset_qUnitHull : Prop
  unitIntegrality : Prop
  coefficientNormalization : Prop

/-- Exact unit-correction gap requirement. -/
def GenericQPilotRegionUnitCorrectionGapRequired : Prop :=
  Nonempty (GenericQPilotRegionUnitCorrectionGap (G := G))

end LeanFormal.IUT.XiFPaper.GenericQPilotCompletionPowerActual
end
