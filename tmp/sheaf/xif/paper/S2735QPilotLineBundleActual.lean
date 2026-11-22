import tmp.sheaf.xif.paper.ArithmeticLineBundleActual
import tmp.sheaf.xif.paper.S2701GaussianPrimeIdealsActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36GaussianSplitPlaceArithmetic

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaperArithmeticLineBundle
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.XiFPaper.S2701GaussianPrimeIdealsActual

attribute [local instance] Classical.decEq

namespace LeanFormal.IUT.XiFPaper.S2735QPilotLineBundleActual

variable (l : PrimeGeFive)

/-- The concrete source arithmetic data with Fmod = F = K = Q(i). -/
abbrev S2735Arithmetic : InitialThetaArithmeticData l :=
  gaussianInitialThetaArithmeticData l

/-- The explicit q-pilot ideal: product of the two primes above 5 and the two
primes above 2161 in the Gaussian integers. -/
noncomputable def qPilotIdeal :
    Ideal (SourceOK (A := S2735Arithmetic l)) :=
  gaussianFieldFivePrimePlus * gaussianFieldFivePrimeMinus *
    gaussianField2161Plus * gaussianField2161Minus

/-- The exact factorized form of the q-pilot ideal. -/
theorem qPilotIdeal_factorization :
    qPilotIdeal l =
      gaussianFieldFivePrimePlus * gaussianFieldFivePrimeMinus *
        gaussianField2161Plus * gaussianField2161Minus := rfl

/-- The q-pilot fractional ideal line bundle. -/
noncomputable def qPilotLineBundle :
    SourceLineBundle (A := S2735Arithmetic l) :=
  (qPilotIdeal l : FractionalIdeal
    (nonZeroDivisors (SourceOK (A := S2735Arithmetic l)))
    (S2735Arithmetic l).K)

/-- The exact q-pilot source identification used by the structure: the q-pilot
ideal is the product of the four actual bad prime ideals. -/
def QPilotSourceIdentification : Prop :=
  qPilotIdeal l =
    gaussianFieldFivePrimePlus * gaussianFieldFivePrimeMinus *
      gaussianField2161Plus * gaussianField2161Minus

theorem qPilot_source_identification_holds :
    QPilotSourceIdentification l :=
  qPilotIdeal_factorization l

/-- The actual q-pilot line-bundle source packet. -/
noncomputable def qPilotLineBundleSource :
    PaperQPilotLineBundleSource (A := S2735Arithmetic l) where
  qPilotLineBundle := qPilotLineBundle l
  qPilotIdeal := qPilotIdeal l
  qPilot_lineBundle_eq := rfl
  qPilot_source_identification := QPilotSourceIdentification l

theorem qPilotLineBundleSource_lineBundle :
    (qPilotLineBundleSource l).qPilotLineBundle = qPilotLineBundle l := rfl

theorem qPilotLineBundleSource_ideal :
    (qPilotLineBundleSource l).qPilotIdeal = qPilotIdeal l := rfl

/-- The stored source identification proposition is exactly the factorized
q-pilot ideal identity. -/
theorem qPilotLineBundleSource_source_identification :
    (qPilotLineBundleSource l).qPilot_source_identification := by
  change QPilotSourceIdentification l
  exact qPilot_source_identification_holds l

/-- q-pilot ideal extended by an arbitrary finite ABC-support factor.  This is
the interface for the later hweightvol support: the bad-prime q-pilot part is
fixed, and the remaining finite ABC support is supplied as `J`. -/
noncomputable def qPilotIdealExtended
    (J : Ideal (SourceOK (A := S2735Arithmetic l))) :
    Ideal (SourceOK (A := S2735Arithmetic l)) :=
  qPilotIdeal l * J

theorem qPilotIdeal_dvd_extended
    (J : Ideal (SourceOK (A := S2735Arithmetic l))) :
    qPilotIdeal l ∣ qPilotIdealExtended l J := by
  exact ⟨J, rfl⟩

/-- The extended q-pilot fractional line bundle. -/
noncomputable def qPilotLineBundleExtended
    (J : Ideal (SourceOK (A := S2735Arithmetic l))) :
    SourceLineBundle (A := S2735Arithmetic l) :=
  (qPilotIdealExtended l J : FractionalIdeal
    (nonZeroDivisors (SourceOK (A := S2735Arithmetic l)))
    (S2735Arithmetic l).K)



abbrev S2735O : Type := SourceOK (A := S2735Arithmetic l)

noncomputable def qPilotP5plus : IsDedekindDomain.HeightOneSpectrum (S2735O l) where
  asIdeal := gaussianFieldFivePrimePlus
  isPrime := gaussianFieldFivePrimePlus_isMaximal.isPrime
  ne_bot := Ring.ne_bot_of_isMaximal_of_not_isField gaussianFieldFivePrimePlus_isMaximal
    (NumberField.RingOfIntegers.not_isField (S2735Arithmetic l).K)

noncomputable def qPilotP5minus : IsDedekindDomain.HeightOneSpectrum (S2735O l) where
  asIdeal := gaussianFieldFivePrimeMinus
  isPrime := gaussianFieldFivePrimeMinus_isMaximal.isPrime
  ne_bot := Ring.ne_bot_of_isMaximal_of_not_isField gaussianFieldFivePrimeMinus_isMaximal
    (NumberField.RingOfIntegers.not_isField (S2735Arithmetic l).K)

noncomputable def qPilotP2161plus : IsDedekindDomain.HeightOneSpectrum (S2735O l) where
  asIdeal := gaussianField2161Plus
  isPrime := gaussianField2161Plus_isMaximal.isPrime
  ne_bot := Ring.ne_bot_of_isMaximal_of_not_isField gaussianField2161Plus_isMaximal
    (NumberField.RingOfIntegers.not_isField (S2735Arithmetic l).K)

noncomputable def qPilotP2161minus : IsDedekindDomain.HeightOneSpectrum (S2735O l) where
  asIdeal := gaussianField2161Minus
  isPrime := gaussianField2161Minus_isMaximal.isPrime
  ne_bot := Ring.ne_bot_of_isMaximal_of_not_isField gaussianField2161Minus_isMaximal
    (NumberField.RingOfIntegers.not_isField (S2735Arithmetic l).K)

/-- Bad-only support marker: the finite support of the q-pilot line bundle is
contained in the four actual bad primes.  This is the support gate; the
fractional-ideal count equality is the remaining proof obligation. -/
def QPilotBadOnlySupport : Prop :=
  forall v : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers (S2735Arithmetic l).K),
    FractionalIdeal.count (S2735Arithmetic l).K v (qPilotLineBundle l) ≠ 0 ->
      v.asIdeal = gaussianFieldFivePrimePlus ∨
      v.asIdeal = gaussianFieldFivePrimeMinus ∨
      v.asIdeal = gaussianField2161Plus ∨
      v.asIdeal = gaussianField2161Minus

/-- Absolute norm of the q-pilot ideal: product of the four bad prime norms. -/
theorem qPilotIdeal_absNorm :
    Ideal.absNorm (qPilotIdeal l) = 5 * 5 * 2161 * 2161 := by
  change Ideal.absNorm
    (gaussianFieldFivePrimePlus * gaussianFieldFivePrimeMinus *
      gaussianField2161Plus * gaussianField2161Minus :
        Ideal gaussianRingOfIntegers) = 5 * 5 * 2161 * 2161
  rw [map_mul, map_mul, map_mul,
    gaussianFieldFivePrimePlus_absNorm, gaussianFieldFivePrimeMinus_absNorm,
    gaussianField2161Plus_absNorm, gaussianField2161Minus_absNorm]

/-- Absolute norm of the q-pilot fractional line bundle. -/
theorem qPilotFractional_absNorm :
    FractionalIdeal.absNorm (qPilotLineBundle l) = (5 * 5 * 2161 * 2161 : ℚ) := by
  rw [qPilotLineBundle, FractionalIdeal.coeIdeal_absNorm, qPilotIdeal_absNorm]
  norm_num

#check qPilotIdeal
#check qPilotLineBundle
#check QPilotSourceIdentification
#check qPilotLineBundleSource
#print axioms qPilotLineBundleSource

end LeanFormal.IUT.XiFPaper.S2735QPilotLineBundleActual
end
