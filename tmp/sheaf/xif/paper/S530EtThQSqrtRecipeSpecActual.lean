import tmp.sheaf.xif.paper.S509OddLiftChoiceActual

-- S530 field-level recipe spec from EtTh Theorem 1.10 / Cor 2.8 / Rem 1.10.1
-- and notesoniut line 869: theta monoid splitting via evaluation at the
-- special 2-torsion point, with qHalf = Theta^l up to mu_{2l}.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.S530EtThQSqrtRecipeSpecActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S485TateTwoTorsionQSqrtActual
open LeanFormal.IUT.XiFPaper.S509OddLiftChoiceActual
open LeanFormal.IUT.XiFPaper.S494TateTwoTorsionConverseGapActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

-- Field-level recipe: a special 2-torsion point giving an evaluation
-- splitting of the theta monoid; Theta^l is the q-half-root.
structure EtThThetaSplittingRecipe (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) where
  specialPoint : ConversePoint T b
  specialPoint_two_torsion : specialPoint + specialPoint = 0
  specialPoint_component_condition : Prop
  evalPoint : ConversePoint T b
  evalPoint_is_translate : Prop
  thetaUnit : (ACF T b)ˣ
  theta_pow : thetaUnit ^ (2 * l.value) = qUnit T b
  qHalfUnit : (ACF T b)ˣ
  qHalf_eq_theta_pow : qHalfUnit = thetaUnit ^ l.value
  qHalf_sq : qHalfUnit ^ 2 = qUnit T b
  evalSplitting : Prop
  kummerClass_eq : Prop
  mu2l_ambiguity : Prop
  normalization_by_special_point : Prop

-- The actual q-sqrt -> 2-torsion compatibility already supplies the
-- reverse direction for the chosen qHalfRoot.
#check qSqrtTwoTorsionData
#check qSqrtOddLiftCondition
#check EtThThetaSplittingRecipe

end LeanFormal.IUT.XiFPaper.S530EtThQSqrtRecipeSpecActual

end