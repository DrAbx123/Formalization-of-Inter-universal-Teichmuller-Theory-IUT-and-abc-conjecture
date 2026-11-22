import tmp.sheaf.xif.paper._S1927Cone1
import tmp.sheaf.xif.paper.S1895OIdentificationsActual
import tmp.sheaf.xif.paper.OneColumnFinitePrimePlaceActual
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellIQTensorPacket
import LeanFormal.IUT.Foundations.Arithmetic.NormLog

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open IsDedekindDomain NumberField
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.OneColumnFinitePrimePlaceActual

namespace ProbeAttach2

abbrev fmod (D : S1895PaperInput) : Type := (S1895PaperInput.I D).initial.arithmetic.Fmod

noncomputable def paperGlobalRealifiedFrobenioid
    (D : S1895PaperInput) : Iut.FrobenioidPresentation :=
  S1927Real.numberFieldFrobenioidPresentationRealified (F := fmod D)

theorem paperGlobalRealifiedFrobenioid_divisorMonoid
    (D : S1895PaperInput) :
    ((paperGlobalRealifiedFrobenioid D).preFrobenioid.divisorMonoid.obj
      LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceModelBackend.bottomPoint).carrier =
      S1927Real.RealEffectiveDivisor (F := fmod D) := rfl

noncomputable def paperBadBasePlace (D : S1895PaperInput)
    (b : (S1895PaperInput.I D).initial.badPlaces) :
    HeightOneSpectrum (NumberField.RingOfIntegers (fmod D)) :=
  b.1.maximalIdeal

noncomputable def paperQVZeroLocusPrime (D : S1895PaperInput)
    (b : (S1895PaperInput.I D).initial.badPlaces) :
    S1927Real.RealEffectiveDivisor (F := fmod D) :=
  (Finsupp.single (paperBadBasePlace D b) (1 : NNReal), fun _ => 0)

noncomputable def paperQVZeroLocusGlobal (D : S1895PaperInput) :
    S1927Real.RealEffectiveDivisor (F := fmod D) :=
  letI := (S1895PaperInput.I D).initial.bad_finite
  ∑ b : (S1895PaperInput.I D).initial.badPlaces, paperQVZeroLocusPrime D b

theorem paperQVZeroLocusGlobal_eq_sum (D : S1895PaperInput) :
    paperQVZeroLocusGlobal D =
      letI := (S1895PaperInput.I D).initial.bad_finite
      ∑ b : (S1895PaperInput.I D).initial.badPlaces, paperQVZeroLocusPrime D b := rfl

noncomputable def paperLogShellDatum (v : FinitePrimePlace 2 7) :
    SourceLogShellDatum where
  p := v.1
  hp := v.2.2.2
  K := Real
  Units := (actualLocalField v)ˣ
  invariants := ⊤
  logMap := unitNormLogDegree (actualLocalField v)

noncomputable def paperGlobalLogShellFamily :
    FinitePrimePlace 2 7 → SourceLogShellDatum :=
  paperLogShellDatum

noncomputable def paperGlobalLogShellPacket :
    Submodule ℚ (FinitePrimePlace 2 7 → Real) :=
  sourceLogShellIQDirectSumPacket paperGlobalLogShellFamily

theorem paperGlobalLogShellPacket_eq_span :
    paperGlobalLogShellPacket =
      Submodule.span ℚ
        (sourceLogShellDirectSumPacketSet paperGlobalLogShellFamily) :=
  sourceLogShellIQDirectSumPacket_eq_span_pi paperGlobalLogShellFamily

noncomputable def paperGlobalLogShellTensorPacket
    {A : Type} [Fintype A] (t : A → Set Real) : Set Real :=
  sourceLogShellTensorProductSet t

theorem paperGlobalLogShellTensorPacket_span_eq
    {A : Type} [Fintype A] [DecidableEq A] (t : A → Set Real) :
    Submodule.span ℚ (paperGlobalLogShellTensorPacket t) =
      Submodule.span ℚ
        (paperGlobalLogShellTensorPacket
          (fun a => (Submodule.span ℚ (t a) : Set Real))) :=
  sourceLogShellTensorProductSet_span_eq t

structure ArchimedeanLogShellDatum where
  K : Type
  [fieldK : Field K]
  [charZeroK : CharZero K]
  [moduleK : Module Real K]
  [topologicalSpaceK : TopologicalSpace K]
  unitBall : Set K
  logShell : Set K
  logShell_subset_unitBall : logShell ⊆ unitBall
  convex_logShell : Convex Real logShell
  isCompact_logShell : IsCompact logShell

attribute [instance] ArchimedeanLogShellDatum.fieldK
  ArchimedeanLogShellDatum.charZeroK ArchimedeanLogShellDatum.moduleK
  ArchimedeanLogShellDatum.topologicalSpaceK

def S1927FirstMissing (D : S1895PaperInput) : Type 1 :=
  ArchimedeanLogShellDatum

example (D : S1895PaperInput) :
    ((paperGlobalRealifiedFrobenioid D).preFrobenioid.divisorMonoid.obj
      LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceModelBackend.bottomPoint).carrier =
      S1927Real.RealEffectiveDivisor (F := fmod D) := rfl

#check paperGlobalLogShellPacket_eq_span
#check paperQVZeroLocusGlobal_eq_sum

#print axioms paperGlobalRealifiedFrobenioid
#print axioms paperGlobalLogShellPacket_eq_span
#print axioms paperQVZeroLocusGlobal_eq_sum

end ProbeAttach2

