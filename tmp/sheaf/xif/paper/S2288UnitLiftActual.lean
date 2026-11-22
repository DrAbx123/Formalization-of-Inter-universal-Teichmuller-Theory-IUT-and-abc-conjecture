import tmp.sheaf.xif.paper.S2286StripChainActual

/-! # S2288: unit log-Kummer lift and the quotient-section gap

An endomorphism of the torsion quotient does not canonically lift to a unit
endomorphism.  A multiplicative section of the quotient map would give the lift
by `u |-> section (f (quotientMap u))`; the section is the exact missing datum.
No section or lift is fabricated. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2288UnitLiftActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S2219PaperOUnitsCarrierActual
open LeanFormal.IUT.XiFPaper.S2249LogKummerTransportActual
open LeanFormal.IUT.XiFPaper.S2286StripChainActual
open LeanFormal.IUT.XiFPaper.S2135Layer1SplitActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Exact missing datum: a multiplicative section of the torsion quotient map. -/
structure S2288QuotientSectionRequired
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) where
  toUnit : S2219PaperOUnitsMu T b → S2219PaperOUnits T b
  toUnit_quotient : ∀ x, s2219QuotientMap T b (toUnit x) = x
  toUnit_one : toUnit 1 = 1
  toUnit_mul : ∀ x y, toUnit (x * y) = toUnit x * toUnit y

/-- A multiplicative quotient section and a quotient automorphism give the
actual unit endomorphism required by S2249. -/
noncomputable def s2288UnitMapOfSection
    (S : S2288QuotientSectionRequired T b)
    (f : S2219PaperOUnitsMu T b ≃* S2219PaperOUnitsMu T b) :
    S2219PaperOUnits T b →* S2219PaperOUnits T b where
  toFun u := S.toUnit (f (s2219QuotientMap T b u))
  map_one' := by
    simp [S.toUnit_one]
  map_mul' := by
    intro u v
    simp [S.toUnit_mul]

theorem s2288UnitMapOfSection_quotientMap
    (S : S2288QuotientSectionRequired T b)
    (f : S2219PaperOUnitsMu T b ≃* S2219PaperOUnitsMu T b)
    (u : S2219PaperOUnits T b) :
    s2219QuotientMap T b (s2288UnitMapOfSection T b S f u) =
      f (s2219QuotientMap T b u) :=
  S.toUnit_quotient _

/-- The section plus S2286's quotient automorphism fills the S2249 unit lift. -/
noncomputable def s2288LogKummerOnUnitsOfSection
    (S : S2288QuotientSectionRequired T b)
    (f : S2219PaperOUnitsMu T b ≃* S2219PaperOUnitsMu T b) :
    S2249LogKummerOnUnitsRequired T b where
  muAut := f
  unitMap := s2288UnitMapOfSection T b S f
  compat := s2288UnitMapOfSection_quotientMap T b S f

/-- The full lift required by S2249, with compatibility. -/
structure S2288UnitLiftRequired
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) where
  muAut : S2219PaperOUnitsMu T b ≃* S2219PaperOUnitsMu T b
  unitMap : S2219PaperOUnits T b →* S2219PaperOUnits T b
  compat : ∀ u : S2219PaperOUnits T b,
    s2219QuotientMap T b (unitMap u) = muAut (s2219QuotientMap T b u)

def S2288UnitLiftRequiredProp
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) : Prop :=
  Nonempty (S2288UnitLiftRequired T b)

/-- S2135 plus a quotient section fills the full S2249 unit lift using S2286. -/
noncomputable def s2288LogKummerOnUnitsOfStripAndSection
    (h : S2135PrimeAlignmentRequired T b)
    (S : S2288QuotientSectionRequired T b) :
    S2249LogKummerOnUnitsRequired T b :=
  s2288LogKummerOnUnitsOfSection T b S (s2286MuAut T b h)

/-- Remaining data: S2135 and a multiplicative section of the torsion quotient. -/
structure S2288RemainingRequired
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) where
  primeAlignment : S2135PrimeAlignmentRequired T b
  quotientSection : S2288QuotientSectionRequired T b

#check s2288LogKummerOnUnitsOfStripAndSection
#check S2288RemainingRequired
#check S2288QuotientSectionRequired
#check s2288UnitMapOfSection
#check s2288UnitMapOfSection_quotientMap
#check s2288LogKummerOnUnitsOfSection
#check S2288UnitLiftRequired
#check S2288UnitLiftRequiredProp

end LeanFormal.IUT.XiFPaper.S2288UnitLiftActual
end
