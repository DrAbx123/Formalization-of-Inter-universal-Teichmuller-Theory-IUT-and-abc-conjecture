import tmp.sheaf.xif.paper._S1927Cone1
import tmp.sheaf.xif.paper.S1895OIdentificationsActual
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellIQTensorPacket

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.OneColumnFinitePrimePlaceActual


namespace ProbeAttach

abbrev fmod (D : S1895PaperInput) : Type := (S1895PaperInput.I D).initial.arithmetic.Fmod

noncomputable def pres (D : S1895PaperInput) : Iut.FrobenioidPresentation :=
  S1927Real.numberFieldFrobenioidPresentationRealified (F := fmod D)

noncomputable def zeroLocusPrime (D : S1895PaperInput)
    (b : (S1895PaperInput.I D).initial.badPlaces) :
    S1927Real.RealEffectiveDivisor (F := fmod D) :=
  (Finsupp.single b.1.maximalIdeal (1 : NNReal), fun _ => 0)

noncomputable def zeroLocusGlobal (D : S1895PaperInput) :
    S1927Real.RealEffectiveDivisor (F := fmod D) :=
  letI := (S1895PaperInput.I D).initial.bad_finite
  ∑ b : (S1895PaperInput.I D).initial.badPlaces, zeroLocusPrime D b

noncomputable def logShellDatum (v : FinitePrimePlace 2 7) : SourceLogShellDatum where
  p := v.1
  hp := v.2.2.2
  K := Real
  Units := (actualLocalField v)ˣ
  invariants := ⊤
  logMap := unitNormLogDegree (actualLocalField v)

noncomputable def logShellFamily : FinitePrimePlace 2 7 → SourceLogShellDatum :=
  logShellDatum

noncomputable def logShellPacket :
    Submodule ℚ (FinitePrimePlace 2 7 → Real) :=
  sourceLogShellIQDirectSumPacket logShellFamily

example : logShellPacket = Submodule.span ℚ
    (sourceLogShellDirectSumPacketSet logShellFamily) := by
  unfold logShellPacket
  exact sourceLogShellIQDirectSumPacket_eq_span_pi logShellFamily

end ProbeAttach

