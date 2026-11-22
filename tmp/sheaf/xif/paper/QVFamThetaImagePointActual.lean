import tmp.sheaf.xif.paper.PaperC3RootThetaHullActual
import tmp.sheaf.xif.paper.PaperSourceThetaConsistencyActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Root-valued qVFam paper theta image object

Rebuilt per PAPER_OBJECT_SPEC.md: the paper theta is
  ThetaLabel (positive j) |-> (QRoot_v)^(j^2),
where QRoot_v is the actual 2l-th root of q_v in the algebraic closure, and
the mu_{2l} indeterminacy acts on the root theta points.

The qVFam tensor block is a completion-valued carrier and cannot represent the
root in general. This file therefore works on the actual root extension
carrier `RootThetaCarrier`; the tensor lift is recorded as an exact carrier
gap. The old `j^2*c_root` completion coefficient and any closure-as-hull are
not used.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.QVFamThetaImagePointActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.PaperC3RootThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperSourceThetaConsistencyActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The actual completion-valued geometry built from the qVFamily q; used only
for its actual place and qUnit fields. -/
noncomputable abbrev qVFamThetaGeometry :
    CompletionValuedSourceGeometry (l := l) (K := T.arithmetic.F)
      (p := qVFamTensorP T b) PUnit :=
  paperSourceGeometryFromQ (l := l) T b

/-- Actual algebraic-closure root theta carrier at all qVFamily places. -/
noncomputable abbrev qVFamRootThetaCarrier : Type 1 :=
  RootThetaCarrier (G := qVFamThetaGeometry (l := l) T b)

/-- The paper theta label map: positive representatives only. -/
noncomputable def qVFamRootThetaImagePoint
    (j : ThetaLabel (l := l)) : qVFamRootThetaCarrier (l := l) T b :=
  paperRootThetaImagePointTheta (G := qVFamThetaGeometry (l := l) T b) j

/-- The actual mu_{2l} action on the root theta image point. -/
noncomputable def qVFamRootThetaMuPoint
    (m : Nat) (j : ThetaLabel (l := l)) :
    qVFamRootThetaCarrier (l := l) T b :=
  paperRootThetaMuPoint (G := qVFamThetaGeometry (l := l) T b) m
    (thetaLabelToSigned (l := l) j)

/-- The actual mu_{2l} orbit of a root theta point. -/
noncomputable def qVFamRootThetaMuOrbit
    (j : ThetaLabel (l := l)) :
    Set (qVFamRootThetaCarrier (l := l) T b) :=
  Set.range (fun m : Nat =>
    qVFamRootThetaMuPoint (l := l) T b m j)

/-- Actual lambda-O/scaling hull: union of the mu_{2l} orbits, no closure. -/
noncomputable def qVFamRootThetaHull :
    Set (qVFamRootThetaCarrier (l := l) T b) :=
  Set.iUnion (fun j : ThetaLabel (l := l) =>
    qVFamRootThetaMuOrbit (l := l) T b j)

theorem qVFamRootThetaImagePoint_mem_orbit
    (j : ThetaLabel (l := l)) :
    qVFamRootThetaImagePoint (l := l) T b j ∈
      qVFamRootThetaMuOrbit (l := l) T b j := by
  refine ⟨0, ?_⟩
  funext v
  simp [qVFamRootThetaMuPoint, qVFamRootThetaImagePoint,
    paperRootThetaMuPoint, paperRootThetaImagePointTheta,
    paperRootThetaImagePoint]

theorem qVFamRootThetaImagePoint_mem_hull
    (j : ThetaLabel (l := l)) :
    qVFamRootThetaImagePoint (l := l) T b j ∈
      qVFamRootThetaHull (l := l) T b := by
  exact Set.mem_iUnion.mpr
    ⟨j, qVFamRootThetaImagePoint_mem_orbit (l := l) T b j⟩

/-- Root-valued paper theta image object on the actual extension carrier. -/
structure QVFamThetaRootImagePointData (j : ThetaLabel (l := l)) where
  point : qVFamRootThetaCarrier (l := l) T b
  point_eq : point = qVFamRootThetaImagePoint (l := l) T b j
  mem_orbit : point ∈ qVFamRootThetaMuOrbit (l := l) T b j
  mem_hull : point ∈ qVFamRootThetaHull (l := l) T b

noncomputable def qVFamThetaRootImagePointData
    (j : ThetaLabel (l := l)) :
    QVFamThetaRootImagePointData (l := l) T b j where
  point := qVFamRootThetaImagePoint (l := l) T b j
  point_eq := rfl
  mem_orbit := qVFamRootThetaImagePoint_mem_orbit (l := l) T b j
  mem_hull := qVFamRootThetaImagePoint_mem_hull (l := l) T b j

/-- Exact carrier gap: lifting the root theta object to the completion-valued
qVFam tensor block. No map is fabricated. -/
structure QVFamRootThetaTensorLiftGap where
  rootToTensor : qVFamRootThetaCarrier (l := l) T b → qVFamTensorBlock T b
  compatibility : Prop

/-- The exact tensor-lift gap is nonempty only when a map is supplied. -/
def QVFamRootThetaTensorLiftGapRequired : Prop :=
  Nonempty (QVFamRootThetaTensorLiftGap (l := l) T b)

end LeanFormal.IUT.XiFPaper.QVFamThetaImagePointActual

end
