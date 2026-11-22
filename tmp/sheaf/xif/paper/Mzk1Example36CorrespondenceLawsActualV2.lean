import tmp.sheaf.xif.paper.Mzk1Example36EtThCorrespondenceActual

/-! Mainline: Example36<->EtTh correspondence bundle laws (safe corollaries). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Example36CorrespondenceLawsActualV2

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceThetaGenerator
open LeanFormal.IUT.IUTII.Frobenioid.Example36.ThetaGeneratorFeasibility
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceThetaDivisor
open LeanFormal.IUT.IUTII.Frobenioid.Example36.ThetaSeries
open LeanFormal.IUT.XiFPaper.EtTh05FrobenioidBoundaryActual
open LeanFormal.IUT.XiFPaper.EtTh11ThetaRealizationRowsActual
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open LeanFormal.IUT.XiFPaper.Mzk1Example36EtThCorrespondenceActual

theorem etthExample36_correspondence_thetaCarrier (l : PrimeGeFive) :
    (example36EtThCorrespondence l).thetaCarrier = analyticThetaCarrierConcrete :=
  rfl

theorem etthExample36_theater_distinct (l : PrimeGeFive) :
    analyticThetaTheater l false ≠ analyticThetaTheater l true := by
  intro h
  have hinj := etthExample36_theater_injective l
  exact Bool.false_ne_true (hinj h)

theorem etthExample36_correspondence_q_mem (l : PrimeGeFive) :
    0 < (example36EtThCorrespondence l).thetaCarrier.q ∧
      (example36EtThCorrespondence l).thetaCarrier.q < 1 :=
  etthExample36_concrete_q_mem

end

end LeanFormal.IUT.XiFPaper.Mzk1Example36CorrespondenceLawsActualV2-- force-fresh-a471
