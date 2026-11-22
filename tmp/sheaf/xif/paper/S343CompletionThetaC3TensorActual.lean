/-
INVALID AS PAPER OBJECT (completion 2l-th root audit).

This file depends on a completion 2l-th root q_v^(1/2l) of the qVFamily q
(PaperQRootCard / NatRootSystem (qVUnit ...) / HalfRootInCompletion).
S342QVFamilyRootImpossibleActual proves that this is impossible: the order is
coprime to l while a 2l-th root forces 2l | order.  The conditional records
and consequences below are retained only as invalidated history; they must not
be used as paper objects or as inputs to further constructions.
-/
import tmp.sheaf.xif.paper.S325CompletionThetaMuOrbitActual
import tmp.sheaf.xif.paper.PaperC3TensorBlockActual
import tmp.sheaf.xif.paper.PaperC3SourceQHullRelationActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import Mathlib.RingTheory.RootsOfUnity.Basic
/-! # S343: completion theta image on the actual C3 tensor block
Conditional on R : PaperQRootCard, the completion theta value is embedded as a
pure tensor in the actual PaperC3 tensor block, with the mu_{2l} diagonal tensor
action and its orbit/image union.  No root is faked. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000
namespace LeanFormal.IUT.XiFPaper.S343CompletionThetaC3TensorActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3TensorBlockActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperC3SourceQHullRelationActual
open LeanFormal.IUT.XiFPaper.PaperCompletionThetaValueActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.S325CompletionThetaMuOrbitActual
open LeanFormal.IUT.LocalFieldPadicTensor
open MeasureTheory
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable (R : PaperQRootCard T b)
abbrev C3Block (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) : Type :=
  Block (G := sourceQGeometry (l := l) T b)
/-- Completion theta value embedded as a pure tensor in the C3 block. -/
noncomputable def c3ThetaTensorImagePoint
    (j : ThetaLabel (l := l)) : C3Block T b :=
  finitePadicTensorTprod (p := qVFamTensorP T b)
    (fun _ : Unit => CommonPrimeCompletion ((sourceQGeometry T b).place ()))
    (fun _ => (paperCompletionThetaValue T b R j :
      CommonPrimeCompletion ((sourceQGeometry T b).place ())))
/-- Diagonal mu_{2l} tensor in the C3 block. -/
noncomputable def c3MuTensor
    (zeta : rootsOfUnity (2 * l.value)
      (CommonPrimeCompletion ((sourceQGeometry T b).place ()))) :
    C3Block T b :=
  finitePadicTensorTprod (p := qVFamTensorP T b)
    (fun _ : Unit => CommonPrimeCompletion ((sourceQGeometry T b).place ()))
    (fun _ => ((zeta : (CommonPrimeCompletion ((sourceQGeometry T b).place ()))ˣ) :
      CommonPrimeCompletion ((sourceQGeometry T b).place ())))
/-- Diagonal action on the C3 block. -/
noncomputable def c3MuAction
    (zeta : rootsOfUnity (2 * l.value)
      (CommonPrimeCompletion ((sourceQGeometry T b).place ())))
    (x : C3Block T b) : C3Block T b :=
  c3MuTensor T b zeta * x
/-- Multiplication law of diagonal mu-tensors. -/
theorem c3MuTensor_mul
    (zeta eta : rootsOfUnity (2 * l.value)
      (CommonPrimeCompletion ((sourceQGeometry T b).place ()))) :
    c3MuTensor T b zeta * c3MuTensor T b eta =
      c3MuTensor T b (zeta * eta) := by
  unfold c3MuTensor
  rw [finitePadicTensorTprod_mul_tprod]
  congr 1

/-- The zeta-multiplied C3 theta image point. -/
noncomputable def c3ThetaMuImagePoint
    (zeta : rootsOfUnity (2 * l.value)
      (CommonPrimeCompletion ((sourceQGeometry T b).place ())))
    (j : ThetaLabel (l := l)) : C3Block T b :=
  c3MuAction T b zeta (c3ThetaTensorImagePoint T b R j)
/-- Composition law of the diagonal mu action. -/
theorem c3MuAction_comp
    (zeta eta : rootsOfUnity (2 * l.value)
      (CommonPrimeCompletion ((sourceQGeometry T b).place ())))
    (x : C3Block T b) :
    c3MuAction T b zeta (c3MuAction T b eta x) =
      c3MuAction T b (zeta * eta) x := by
  unfold c3MuAction
  rw [← mul_assoc, c3MuTensor_mul]

/-- mu-orbit of the C3 theta image point at label j. -/
noncomputable def c3ThetaMuOrbit
    (j : ThetaLabel (l := l)) : Set (C3Block T b) :=
  Set.range (fun zeta : rootsOfUnity (2 * l.value)
      (CommonPrimeCompletion ((sourceQGeometry T b).place ())) =>
    c3ThetaMuImagePoint T b R zeta j)
/-- C3 theta image union over labels and mu-orbit. -/
noncomputable def c3ThetaMuImageUnion : Set (C3Block T b) :=
  ⋃ j : ThetaLabel (l := l), c3ThetaMuOrbit T b R j
end LeanFormal.IUT.XiFPaper.S343CompletionThetaC3TensorActual
