import tmp.sheaf.xif.paper.Mzk1P0LRegionOpenActual
import tmp.sheaf.xif.paper.Mzk1P0LRegionNonemptyActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0LRegionMassFinalActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.Mzk1P0LPaperInstanceActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LRegionPosActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LRegionNonemptyActual
variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)
theorem regionMass_pos_of_open_final
    (hopen : IsOpen (actualC3LogShellTensorRegionL (C3LAt I place))) :
    0 < actualC3LogShellTensorHaarL (C3LAt I place)
      (actualC3LogShellTensorRegionL (C3LAt I place)) :=
  regionMass_pos_of_isOpen_of_nonempty I place hopen (thetaRegion_nonempty I place)
end LeanFormal.IUT.XiFPaper.Mzk1P0LRegionMassFinalActual