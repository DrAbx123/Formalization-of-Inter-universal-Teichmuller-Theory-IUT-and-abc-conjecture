import tmp.sheaf.xif.paper.Mzk1Example36EtThCorrespondenceActual

/-! Mainline: Example36<->EtTh correspondence bundle laws (real projections/injectivity
  corollaries; the named row-6 manifestation is untouched). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Example36CorrespondenceLawsActual

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

/-- Theta-carrier projection of the correspondence bundle. -/
theorem etthExample36_correspondence_thetaCarrier (l : PrimeGeFive) :
    (example36EtThCorrespondence l).thetaCarrier = analyticThetaCarrierConcrete :=
  rfl

/-- The two-theater family separates the two theaters. -/
theorem etthExample36_theater_distinct (l : PrimeGeFive) :
    analyticThetaTheater l false ≠ analyticThetaTheater l true := by
  intro h
  have hinj := etthExample36_theater_injective l
  exact Bool.false_ne_true (hinj h)

/-- Concrete expansion coefficients re-export at the correspondence level. -/
theorem etthExample36_correspondence_expansion (l : PrimeGeFive) (n : ℤ) :
    ((analyticThetaQExpansion (example36EtThCorrespondence l).thetaCarrier n : ℝ) : ℂ) =
      qExpansionTerm n :=
  etthExample36_concrete_expansion_eq_jacobi n

/-- The correspondence q-parameter stays in (0,1). -/
theorem etthExample36_correspondence_q_mem (l : PrimeGeFive) :
    0 < (example36EtThCorrespondence l).thetaCarrier.q ∧
      (example36EtThCorrespondence l).thetaCarrier.q < 1 := by
  rw [etthExample36_correspondence_thetaCarrier l]
  exact etthExample36_concrete_q_mem

/-- Correspondence-level kernel identity: q-expansion value = Gaussian kernel value. -/
theorem etthExample36_correspondence_kernel (l : PrimeGeFive) (n : ℤ) :
    analyticThetaQExpansion (example36EtThCorrespondence l).thetaCarrier n =
      realThetaValue (example36EtThCorrespondence l).thetaCarrier.q n :=
  rfl

/-- Correspondence-level generator card nonemptiness (`SourceThetaGeneratorCard` is a
  Type, inhabited by the concrete analytic generator data). -/
theorem etthExample36_correspondence_generatorCard_nonempty (l : PrimeGeFive) :
    Nonempty (SourceThetaGeneratorCard l) :=
  etthExample36_thetaGeneratorCard_nonempty l

/-- The correspondence q-parameter is nonzero. -/
theorem etthExample36_correspondence_q_ne_zero (l : PrimeGeFive) :
    (example36EtThCorrespondence l).thetaCarrier.q ≠ 0 :=
  ne_of_gt (etthExample36_correspondence_q_mem l).1

/-- The correspondence q-parameter is below one. -/
theorem etthExample36_correspondence_q_lt_one (l : PrimeGeFive) :
    (example36EtThCorrespondence l).thetaCarrier.q < 1 :=
  (etthExample36_correspondence_q_mem l).2

end

end LeanFormal.IUT.XiFPaper.Mzk1Example36CorrespondenceLawsActual