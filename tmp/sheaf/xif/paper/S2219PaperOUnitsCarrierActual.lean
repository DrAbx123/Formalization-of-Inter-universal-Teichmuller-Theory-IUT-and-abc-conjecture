import tmp.sheaf.xif.paper.S2202NotInBaseActual
import tmp.sheaf.xif.paper.S2040PaperOtriFromS2092Actual
import LeanFormal.IUT.IUTII.Kummer.TimesMuQuotient

/-! # S2219: the paper O^× / O^×μ carrier choice

Paper semantics (IUT I, §1; recorded in S2035): for `L_v = F̄_v`, the paper's
local `O^×` is the unit group of the integral ring `Integers L_v`, not the
`K_v`-unit group `(Integers K_v)^×` of S2092.  Accordingly we select

  `S2219PaperOUnits := S2147PaperIntegralClosureOUnits`,
  `S2219PaperOUnitsMu := TimesMuQuotient S2219PaperOUnits`,

with the actual action of S2147/S2202 and its descended quotient action. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2219PaperOUnitsCarrierActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1413SourceKPlaceQComparisonActual
open LeanFormal.IUT.XiFPaper.S2147PaperIntegralClosureOUnitsActionActual
open LeanFormal.IUT.XiFPaper.S2202NotInBaseActual
open LeanFormal.IUT.XiFPaper.S2092PaperOtriActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Selected paper O^×: integral-closure units. -/
abbrev S2219PaperOUnits : Type :=
  S2147PaperIntegralClosureOUnits T b

/-- Selected paper O^×μ: the torsion quotient. -/
abbrev S2219PaperOUnitsMu : Type :=
  TimesMuQuotient (S2219PaperOUnits T b)

/-- Actual quotient map O^× → O^×μ. -/
noncomputable def s2219QuotientMap :
    S2219PaperOUnits T b →* S2219PaperOUnitsMu T b :=
  TimesMuQuotient.quotientMap

theorem s2219QuotientMap_ker :
    MonoidHom.ker (s2219QuotientMap T b) =
      CommGroup.torsion (S2219PaperOUnits T b) :=
  TimesMuQuotient.quotientMap_ker

theorem s2219QuotientMap_surjective :
    Function.Surjective (s2219QuotientMap T b) :=
  TimesMuQuotient.quotientMap_surjective

/-- Actual local Galois action on the selected paper O^×. -/
noncomputable def s2219GaloisAction :
    S2147PaperIntegralClosureGaloisGroup T b →*
      MulAut (S2219PaperOUnits T b) :=
  s2147PaperIntegralClosureOUnitsGaloisAction T b

/-- Descended actual action on paper O^×μ. -/
noncomputable def s2219OUnitsMuAction :
    S2147PaperIntegralClosureGaloisGroup T b →*
      MulAut (S2219PaperOUnitsMu T b) :=
  TimesMuQuotient.action (s2219GaloisAction T b)

theorem s2219OUnitsMuAction_quotientMap
    (σ : S2147PaperIntegralClosureGaloisGroup T b)
    (u : S2219PaperOUnits T b) :
    s2219OUnitsMuAction T b σ (s2219QuotientMap T b u) =
      s2219QuotientMap T b (s2219GaloisAction T b σ u) :=
  TimesMuQuotient.action_quotientMap (s2219GaloisAction T b) σ u

/-- The actual action is nontrivial (S2202). -/
theorem s2219NontrivialAction :
    ∃ (σ : S2147PaperIntegralClosureGaloisGroup T b)
      (u : S2219PaperOUnits T b),
        s2219GaloisAction T b σ u ≠ u :=
  s2202NontrivialAction T b

/-- The selected carrier is not the S2092 K_v-unit carrier: the latter is the
fixed/base unit subgroup, while the paper carrier is the integral-closure units
carrying the genuine action.  This is the formal choice record. -/
structure S2219CarrierChoice where
  OUnits := S2219PaperOUnits T b
  OUnitsMu := S2219PaperOUnitsMu T b
  quotientMap := s2219QuotientMap T b
  galoisAction := s2219GaloisAction T b
  muAction := s2219OUnitsMuAction T b
  nontrivial_action : Prop

noncomputable def s2219CarrierChoice : S2219CarrierChoice T b where
  nontrivial_action := ∃ (σ : S2147PaperIntegralClosureGaloisGroup T b)
      (u : S2219PaperOUnits T b), s2219GaloisAction T b σ u ≠ u

theorem s2219CarrierChoice_nontrivial :
    (s2219CarrierChoice T b).nontrivial_action := s2219NontrivialAction T b

#check S2219PaperOUnits
#check S2219PaperOUnitsMu
#check s2219QuotientMap
#check s2219QuotientMap_ker
#check s2219QuotientMap_surjective
#check s2219GaloisAction
#check s2219OUnitsMuAction
#check s2219OUnitsMuAction_quotientMap
#check s2219NontrivialAction
#check s2219CarrierChoice

end LeanFormal.IUT.XiFPaper.S2219PaperOUnitsCarrierActual
end
