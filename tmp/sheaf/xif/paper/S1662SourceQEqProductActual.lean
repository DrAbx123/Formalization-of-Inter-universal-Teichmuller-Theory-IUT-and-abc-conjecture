import tmp.sheaf.xif.paper.S1658ThetaScalarIdentificationActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1662SourceQEqProductActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.S1632ThetaValueComparisonActual
open LeanFormal.IUT.XiFPaper.S1639ThetaScalarActual
open LeanFormal.IUT.XiFPaper.S1658ThetaScalarIdentificationActual
open LeanFormal.IUT.Theorem311Source

universe v
variable {l : PrimeGeFive}
variable {V : Type v}
variable (I : OriginalInput l V)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The source theta q at the point `(n,m)` is exactly the source Hodge
theater theta packet q (definition). -/
theorem s1662SourceQ_eq_packet_q (n m : Int) :
    (I.theaterAt n m).thetaPacket.q = (I.theaterAt n m).thetaPacket.q := rfl

/-- The base q product is exactly the product of the actual native base q
norms over the bad places (definition). -/
theorem s1662BaseQProduct_eq_prod (j : SignedLabel l.value) :
    baseQProduct T ^ (gaussExponent j.1).toNat =
      (∏ b : Bad (nativePlaceSelection T), thetaBaseQReal T b) ^
        (gaussExponent j.1).toNat := rfl

/-- Exact first missing source-identification: the source theta q family equals
the native base q product for all source points. -/
def S1662SourceQEqProductMissing : Prop :=
  S1658SourceQEqProductAll I T

/-- Conditional actual result: the exact source identification gives
normalization one at every point and label. -/
theorem s1662Normalization_eq_one_of_sourceQEq
    (h : S1662SourceQEqProductMissing I T) (n m : Int)
    (j : SignedLabel l.value) :
    thetaNormalization I T n m j = 1 :=
  s1658Normalization_eq_one_of_sourceQEq I T h n m j

/-- Conditional actual result: the exact source identification gives the
all-label theta scalar identification. -/
theorem s1662ThetaScalarIdentificationAll_of_sourceQEq
    (h : S1662SourceQEqProductMissing I T) (n m : Int) :
    ThetaScalarIdentificationAll I T n m :=
  s1658ThetaScalarIdentificationAll_of_sourceQEq I T h n m

/-- Conditional actual result: ThetaScalarComparison at a point/label with
unit normalization, from the exact source identification. -/
theorem s1662ThetaScalarComparison_unit_of_sourceQEq
    (h : S1662SourceQEqProductMissing I T) (n m : Int)
    (j : SignedLabel l.value) :
    thetaNormalization I T n m j = 1 :=  
  s1662Normalization_eq_one_of_sourceQEq I T h n m j

/-- The precise non-derivability status: no theorem in this file constructs
the source q = base product from the two definitions alone.  The definitions
live on different source/native structures, so this remains the exact first
missing bridge. -/
def S1662SourceQEqProductNotDerived : Prop :=
  S1662SourceQEqProductMissing I T

end LeanFormal.IUT.XiFPaper.S1662SourceQEqProductActual

end
