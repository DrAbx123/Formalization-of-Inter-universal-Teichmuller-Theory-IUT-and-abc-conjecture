import tmp.sheaf.xif.paper.S1729FullBadPlaceActual
import tmp.sheaf.xif.paper.S1727SectionsFPrimeActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31PlacePartition

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1724PaperArithmeticActual
open LeanFormal.IUT.XiFPaper.S1729FullBadPlaceActual
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.Definition31PlacePartition
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.Theorem311Source

namespace LeanFormal.IUT.XiFPaper.S1730SourceDataConditionalActual

variable (l : PrimeGeFive)

/-- The actual arithmetic input A = S1724InitialThetaArithmeticData l. -/
abbrev S1730A : InitialThetaArithmeticData l := S1724InitialThetaArithmeticData l

/-- The actual selected/bad places over A, with full bad set {3,5,7}. -/
abbrev S1730Selection : SourcePlaceSelection (S1730A l) := S1729Selection l

/-- The actual bad-place reduction cards over A. -/
abbrev S1730ReductionCards : BadPlaceReductionCards (S1730Selection l) :=
  S1729BadPlaceReductionCards l

/-- The actual reduction clause over A. -/
abbrev S1730ReductionClause :
    SourceReductionClause (Selected (S1730Selection l)) (Bad (S1730Selection l)) :=
  S1729FullReductionClause l

/-- Conditional SourceDefinition31Data: arithmetic, selected/bad places and
reduction are actual; the four remaining clauses and five compatibility
pairs are explicit inputs. -/
noncomputable def S1730SourceData
    (T : SourceTorsionClause.{0, 0, 0} l)
    (O : SourceOrbicurveClause.{0, 0, 0})
    (Se : SourceSectionClause.{0, 0, 0})
    (Cu : SourceCuspClause)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    SourceDefinition31Data.{0} l :=
  d11EntryData (S1730Selection l) (S1730ReductionCards l)
    T O Se Cu redCompat hredCompat torCompat htorCompat
    orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat

@[simp] theorem S1730SourceData_arithmetic
    (T : SourceTorsionClause.{0, 0, 0} l)
    (O : SourceOrbicurveClause.{0, 0, 0})
    (Se : SourceSectionClause.{0, 0, 0})
    (Cu : SourceCuspClause)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    (S1730SourceData l T O Se Cu redCompat hredCompat torCompat htorCompat
      orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat).arithmetic =
      S1730A l := rfl

@[simp] theorem S1730SourceData_selectedPlaces
    (T : SourceTorsionClause.{0, 0, 0} l)
    (O : SourceOrbicurveClause.{0, 0, 0})
    (Se : SourceSectionClause.{0, 0, 0})
    (Cu : SourceCuspClause)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    (S1730SourceData l T O Se Cu redCompat hredCompat torCompat htorCompat
      orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat).selectedPlaces =
      Selected (S1730Selection l) := rfl

#check S1730SourceData
#check S1730SourceData_arithmetic
#print axioms S1730SourceData
end LeanFormal.IUT.XiFPaper.S1730SourceDataConditionalActual
end