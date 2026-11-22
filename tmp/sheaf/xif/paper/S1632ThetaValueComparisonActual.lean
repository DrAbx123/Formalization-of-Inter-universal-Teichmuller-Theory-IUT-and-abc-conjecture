import tmp.sheaf.xif.paper.BaseQFamilyActual
import tmp.sheaf.xif.paper.BaseQLogVolumeActual
import LeanFormal.IUT.Foundations.Theta.GaussianKernel

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1632ThetaValueComparisonActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual
open LeanFormal.IUT.Theorem311Source

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The actual real local q_v at a bad place. -/
noncomputable def thetaBaseQReal (b : Bad (nativePlaceSelection T)) : Real :=
  ‖(nativeBaseQFamily T b).q‖

theorem thetaBaseQReal_pos (b : Bad (nativePlaceSelection T)) :
    0 < thetaBaseQReal T b :=
  norm_pos_iff.mpr (nativeBaseQFamily T b).q_ne_zero

/-- The actual scalar map q_v^(j^2) in the real value field. -/
noncomputable def thetaScalarMap (b : Bad (nativePlaceSelection T))
    (j : SignedLabel l.value) : Real :=
  (thetaBaseQReal T b) ^ (gaussExponent j.1).toNat

theorem thetaScalarMap_pos (b : Bad (nativePlaceSelection T))
    (j : SignedLabel l.value) : 0 < thetaScalarMap T b j :=
  pow_pos (thetaBaseQReal_pos T b) _

/-- The actual global product of q_v^(j^2) over the bad places. -/
noncomputable def thetaProductValue (j : SignedLabel l.value) : Real :=
  ∏ b : Bad (nativePlaceSelection T), thetaScalarMap T b j

theorem thetaProductValue_pos (j : SignedLabel l.value) :
    0 < thetaProductValue T j :=
  Finset.prod_pos (fun b _ => thetaScalarMap_pos T b j)

/-- Faithful theta-value object: theta section values at labels, actual
q_v^(j^2) scalar maps, and the normalization comparison. -/
structure ThetaValueObject where
  thetaSectionValue : SignedLabel l.value → Real
  scalarMap : Bad (nativePlaceSelection T) → SignedLabel l.value → Real
  scalarMap_eq : ∀ b j, scalarMap b j = thetaScalarMap T b j
  normalization : Real
  normalization_ne_zero : normalization ≠ 0
  thetaValue_eq : ∀ j,
    thetaSectionValue j = normalization * thetaProductValue T j

noncomputable def thetaValueObjectOfData
    (thetaSectionValue : SignedLabel l.value → Real)
    (normalization : Real) (hnormalization : normalization ≠ 0)
    (hvalue : ∀ j,
      thetaSectionValue j = normalization * thetaProductValue T j) :
    ThetaValueObject T where
  thetaSectionValue := thetaSectionValue
  scalarMap := thetaScalarMap T
  scalarMap_eq := fun _ _ => rfl
  normalization := normalization
  normalization_ne_zero := hnormalization
  thetaValue_eq := hvalue

/-- Exact first missing data: theta section value plus normalization comparison.
No inhabitant asserted. -/
def S1632ThetaValueComparisonRequired : Prop :=
  Nonempty (ThetaValueObject T)

end LeanFormal.IUT.XiFPaper.S1632ThetaValueComparisonActual

end
