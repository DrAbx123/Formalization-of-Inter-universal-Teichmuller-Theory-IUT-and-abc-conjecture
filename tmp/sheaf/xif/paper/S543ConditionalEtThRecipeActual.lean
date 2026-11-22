import tmp.sheaf.xif.paper.S531EtThThetaUnitRecipeActual

-- S543: conditional EtThThetaSplittingRecipe.  qHalf = actual thetaUnit^l;
-- special/eval/splitting/normalization are explicit parameters, not faked.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.S543ConditionalEtThRecipeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S485TateTwoTorsionQSqrtActual
open LeanFormal.IUT.XiFPaper.S494TateTwoTorsionConverseGapActual
open LeanFormal.IUT.XiFPaper.S509OddLiftChoiceActual
open LeanFormal.IUT.XiFPaper.S530EtThQSqrtRecipeSpecActual
open LeanFormal.IUT.XiFPaper.S531EtThThetaUnitRecipeActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

noncomputable def conditionalEtThThetaSplittingRecipe
    (specialPoint : ConversePoint T b)
    (specialPoint_two_torsion : specialPoint + specialPoint = 0)
    (specialPoint_component_condition : Prop)
    (evalPoint : ConversePoint T b)
    (evalPoint_is_translate : Prop)
    (evalSplitting : Prop)
    (kummerClass_eq : Prop)
    (mu2l_ambiguity : Prop)
    (normalization_by_special_point : Prop) :
    EtThThetaSplittingRecipe T b where
  specialPoint := specialPoint
  specialPoint_two_torsion := specialPoint_two_torsion
  specialPoint_component_condition := specialPoint_component_condition
  evalPoint := evalPoint
  evalPoint_is_translate := evalPoint_is_translate
  thetaUnit := thetaUnitCandidate T b
  theta_pow := thetaUnitCandidate_pow T b
  qHalfUnit := qHalfUnitCandidate T b
  qHalf_eq_theta_pow := qHalfUnitCandidate_eq T b
  qHalf_sq := qHalfUnitCandidate_sq T b
  evalSplitting := evalSplitting
  kummerClass_eq := kummerClass_eq
  mu2l_ambiguity := mu2l_ambiguity
  normalization_by_special_point := normalization_by_special_point

theorem conditionalRecipe_qHalf_sq
    (specialPoint : ConversePoint T b)
    (specialPoint_two_torsion : specialPoint + specialPoint = 0)
    (specialPoint_component_condition : Prop)
    (evalPoint : ConversePoint T b)
    (evalPoint_is_translate : Prop)
    (evalSplitting : Prop)
    (kummerClass_eq : Prop)
    (mu2l_ambiguity : Prop)
    (normalization_by_special_point : Prop) :
    (conditionalEtThThetaSplittingRecipe T b specialPoint specialPoint_two_torsion
      specialPoint_component_condition evalPoint evalPoint_is_translate
      evalSplitting kummerClass_eq mu2l_ambiguity normalization_by_special_point).qHalfUnit ^ 2
      = qUnit T b := by
  exact qHalfUnitCandidate_sq T b

theorem conditionalRecipe_theta_pow
    (specialPoint : ConversePoint T b)
    (specialPoint_two_torsion : specialPoint + specialPoint = 0)
    (specialPoint_component_condition : Prop)
    (evalPoint : ConversePoint T b)
    (evalPoint_is_translate : Prop)
    (evalSplitting : Prop)
    (kummerClass_eq : Prop)
    (mu2l_ambiguity : Prop)
    (normalization_by_special_point : Prop) :
    (conditionalEtThThetaSplittingRecipe T b specialPoint specialPoint_two_torsion
      specialPoint_component_condition evalPoint evalPoint_is_translate
      evalSplitting kummerClass_eq mu2l_ambiguity normalization_by_special_point).thetaUnit ^
      (2 * l.value) = qUnit T b := by
  exact thetaUnitCandidate_pow T b

-- Exact missing evaluation section: no construction from repo.
structure EtThEvalSectionConstructionGap where
  evalSection : ConversePoint T b → ACF T b
  evalSection_special : Prop
  splitting_equivariant : Prop
  kummerClass_eq_theta_pow : Prop
  normalization_by_special_point : Prop

#check conditionalEtThThetaSplittingRecipe
#check conditionalRecipe_qHalf_sq
#check conditionalRecipe_theta_pow
#check EtThEvalSectionConstructionGap

end LeanFormal.IUT.XiFPaper.S543ConditionalEtThRecipeActual

end