import tmp.sheaf.xif.paper.Mzk1P0LPaperInstanceActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0LRegionPosActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.Mzk1P0LPaperInstanceActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorLActual
open MeasureTheory
variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)
def regionOpenGap : Prop :=
  IsOpen (actualC3LogShellTensorRegionL (C3LAt I place))
def regionNonemptyGap : Prop :=
  (actualC3LogShellTensorRegionL (C3LAt I place)).Nonempty
def regionMassPosGap : Prop :=
  0 < actualC3LogShellTensorHaarL (C3LAt I place)
    (actualC3LogShellTensorRegionL (C3LAt I place))
theorem regionMass_pos_of_isOpen_of_nonempty
    (hopen : IsOpen (actualC3LogShellTensorRegionL (C3LAt I place)))
    (hne : (actualC3LogShellTensorRegionL (C3LAt I place)).Nonempty) :
    0 < actualC3LogShellTensorHaarL (C3LAt I place)
      (actualC3LogShellTensorRegionL (C3LAt I place)) :=
  IsOpen.measure_pos (μ := actualC3LogShellTensorHaarL (C3LAt I place)) hopen hne
end LeanFormal.IUT.XiFPaper.Mzk1P0LRegionPosActual