import tmp.sheaf.xif.paper.KummerEvaluationSquareActual
import tmp.sheaf.xif.paper.ThetaLinkKummerObjectsActual

-- Actual Ind3 / log-Kummer action data
--
-- Source: IUT III, Theorem 3.11, (ii), (Ind3); Proposition 3.10, (ii).
-- As m varies, the Kummer isomorphisms of tensor packets of log-shells are
-- upper-semi-compatible. The actual reduced data constructed here are:
--   * the actual x-mu unit quotient stage at each m;
--   * the actual times-mu (log-shell) action on that stage;
--   * the actual comparison isomorphism from stage m to the core stage 0,
--     induced by the actual F-prime-strip link I.fLinkAt.
-- No inequality/subsets are asserted here; the upper-semi inclusion/surjection
-- itself is not fitted. No sorry/axiom/True/PUnit/toy. WRITE-ONLY: no lake/lean.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Ind3UpperSemiActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.FPrimeStrip
open LeanFormal.IUT.XiFPaper.ThetaLinkKummerObjectsActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

-- The actual x-mu quotient stage at column m and place v.
abbrev ActualInd3Stage (v : V) (m : Int) : Type :=
  TimesMuQuotient ((I.fPrimeStripAt 1 m).Mon v)ˣ

-- The actual times-mu (log-shell) action on the stage.
def actualInd3StageAction (v : V) (m : Int) :
    (I.fPrimeStripAt 1 m).toDPrimeStrip.Pi v →*
      MulAut (ActualInd3Stage (I := I) v m) :=
  (I.fPrimeStripAt 1 m).timesMuAction v

-- The actual comparison isomorphism from stage m to the core stage 0,
-- induced by the actual F-prime-strip link I.fLinkAt 1 m 1 0.
noncomputable def actualInd3StageComparison (v : V) (m : Int) :
    ActualInd3Stage (I := I) v m ≃* ActualInd3Stage (I := I) v 0 :=
  xMuQuotientEquiv (I.fPrimeStripAt 1 m) (I.fPrimeStripAt 1 0)
    (I.fLinkAt 1 m 1 0) v

-- Actual Ind3 action data: actual stages, actual times-mu actions, actual
-- comparison isomorphisms to the core stage.
structure ActualInd3Data (v : V) where
  stage : Int → Type
  stageAction : ∀ m : Int,
    (I.fPrimeStripAt 1 m).toDPrimeStrip.Pi v →* MulAut (stage m)
  stageComparison : ∀ m : Int, stage m ≃* stage 0

-- The actual Ind3 data, constructed from the actual strip actions and links.
noncomputable def actualInd3Data (v : V) : ActualInd3Data (I := I) v where
  stage m := ActualInd3Stage (I := I) v m
  stageAction m := actualInd3StageAction (I := I) v m
  stageComparison m := actualInd3StageComparison (I := I) v m

-- Projection: the actual Ind3 stage is the actual x-mu quotient stage.
theorem actualInd3Data_stage (v : V) (m : Int) :
    (actualInd3Data (I := I) v).stage m = ActualInd3Stage (I := I) v m := rfl

-- Actual transition map stage m -> core stage 0, from the actual comparison.
noncomputable def actualInd3Transition (v : V) (m : Int) :
    ActualInd3Stage (I := I) v m →* ActualInd3Stage (I := I) v 0 :=
  (actualInd3StageComparison (I := I) v m).toMonoidHom

-- Actual action compatibility of the Ind3 transition with the times-mu actions
-- and the actual strip link isoPi: comparison(action_m g x) =
-- action_0 (e.isoPi g) (comparison x).
theorem actualInd3Transition_action_compat (v : V) (m : Int)
    (g : (I.fPrimeStripAt 1 m).toDPrimeStrip.Pi v)
    (x : ActualInd3Stage (I := I) v m) :
    actualInd3Transition (I := I) v m
        (actualInd3StageAction (I := I) v m g x) =
      (I.fPrimeStripAt 1 0).timesMuAction v
        ((I.fLinkAt 1 m 1 0).isoPi v g)
        (actualInd3Transition (I := I) v m x) := by
  refine Quotient.inductionOn x ?_
  intro u
  rw [actualInd3Transition, actualInd3StageAction, actualInd3StageComparison,
    xMuQuotientEquiv, TimesMuQuotient.action_quotientMap,
    TimesMuQuotient.congr_quotientMap, TimesMuQuotient.congr_quotientMap,
    TimesMuQuotient.action_quotientMap]
  apply congrArg TimesMuQuotient.quotientMap
  apply Units.ext
  simp only [Units.coe_mapEquiv, FPrimeStrip.unitsAction_val, MonoidHom.comp_apply]
  exact (I.fLinkAt 1 m 1 0).compatAction v g (u : (I.fPrimeStripAt 1 m).Mon v)

-- Actual Ind3 upper-semi data: actual transition maps, actual injectivity/
-- surjectivity of the comparison, and actual action compatibility. This is
-- the upper-semi comparison data; no inequality/subsets are fitted.
structure ActualInd3UpperSemiData (v : V) where
  transition : ∀ m : Int,
    ActualInd3Stage (I := I) v m →* ActualInd3Stage (I := I) v 0
  transition_injective : ∀ m : Int, Function.Injective (transition m)
  transition_surjective : ∀ m : Int, Function.Surjective (transition m)
  action_compat : ∀ (m : Int)
    (g : (I.fPrimeStripAt 1 m).toDPrimeStrip.Pi v)
    (x : ActualInd3Stage (I := I) v m),
      transition m (actualInd3StageAction (I := I) v m g x) =
        (I.fPrimeStripAt 1 0).timesMuAction v
          ((I.fLinkAt 1 m 1 0).isoPi v g) (transition m x)

-- The actual Ind3 upper-semi data, constructed from the actual comparisons.
noncomputable def actualInd3UpperSemiData (v : V) :
    ActualInd3UpperSemiData (I := I) v where
  transition m := actualInd3Transition (I := I) v m
  transition_injective m := (actualInd3StageComparison (I := I) v m).injective
  transition_surjective m := (actualInd3StageComparison (I := I) v m).surjective
  action_compat m g x := actualInd3Transition_action_compat (I := I) v m g x

-- The actual Ind3 upper-semi image at core stage 0, as the actual range of
-- the transition. This is an actual set, not an inequality judgment.
def actualInd3UpperSemiImage (v : V) (m : Int) :
    Set (ActualInd3Stage (I := I) v 0) :=
  Set.range (actualInd3Transition (I := I) v m)

theorem actualInd3UpperSemiImage_mem (v : V) (m : Int)
    (y : ActualInd3Stage (I := I) v 0) :
    y ∈ actualInd3UpperSemiImage (I := I) v m ↔
      ∃ x : ActualInd3Stage (I := I) v m,
        actualInd3Transition (I := I) v m x = y :=
  Iff.rfl
-- Actual injectivity/surjectivity of the Ind3 transition, from the comparison.
theorem actualInd3Transition_injective (v : V) (m : Int) :
    Function.Injective (actualInd3Transition (I := I) v m) :=
  (actualInd3StageComparison (I := I) v m).injective

theorem actualInd3Transition_surjective (v : V) (m : Int) :
    Function.Surjective (actualInd3Transition (I := I) v m) :=
  (actualInd3StageComparison (I := I) v m).surjective

-- Actual compatibility of the packaged Ind3 data, definitionally from the
-- actual transition/action compatibility.
theorem actualInd3UpperSemiData_action_compat (v : V) (m : Int)
    (g : (I.fPrimeStripAt 1 m).toDPrimeStrip.Pi v)
    (x : ActualInd3Stage (I := I) v m) :
    (actualInd3UpperSemiData (I := I) v).transition m
        (actualInd3StageAction (I := I) v m g x) =
      (I.fPrimeStripAt 1 0).timesMuAction v
        ((I.fLinkAt 1 m 1 0).isoPi v g)
        ((actualInd3UpperSemiData (I := I) v).transition m x) :=
  (actualInd3UpperSemiData (I := I) v).action_compat m g x

#check ActualInd3Stage
#check actualInd3StageAction
#check actualInd3StageComparison
#check ActualInd3Data
#check actualInd3Data
#check actualInd3Data_stage
#check actualInd3Transition
#check actualInd3Transition_action_compat
#check ActualInd3UpperSemiData
#check actualInd3UpperSemiData
#check actualInd3UpperSemiImage
#check actualInd3UpperSemiImage_mem
#check actualInd3Transition_injective
#check actualInd3Transition_surjective
#check actualInd3UpperSemiData_action_compat

end LeanFormal.IUT.XiFPaper.Ind3UpperSemiActual

end