import tmp.sheaf.xif.paper.S1388KappaSourceUnitsActual

-- S1399: paper O^x(G) module/action versus the actual S1388 pair datum.
-- Actual: S1388 actualMiddlePairDatum on the middle strip units, with
-- actual link Kummer representatives (no self/refl, no finite model).
-- Exact: the paper O^x(G) module/action and its identification with the
-- actual middle-strip units; first field recorded, no inhabitant.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1399KappaOxGActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1187NonReflKummerCommonGroupActual
open LeanFormal.IUT.XiFPaper.S1388KappaSourceUnitsActual

universe ua uv upi umon ui uG vV uU

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput l V)

local instance s1399TopS01 : ∀ v : V, TopologicalSpace ((S01 (I := I)).Pi v) :=
  fun _ => ⊥

local instance s1399TopMiddle : TopologicalSpace (MiddleGraph (I := I)) :=
  inferInstance

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- Exact first field: the paper O^x(G) module/action, identified with the
actual middle-strip S01 unit group and its actual units action. -/
structure S1399PaperOxGModule where
  sourceUnits : V → Type uU
  [commGroupSourceUnits : ∀ v, CommGroup (sourceUnits v)]
  sourceAction : ∀ v, G →* MulAut (sourceUnits v)
  groupEquiv : G ≃* MiddleGraph (I := I)
  unitsEquiv : ∀ v, sourceUnits v ≃* ((S01 (I := I)).Mon v)ˣ
  action_compat : ∀ (v : V) (γ : G) (u : sourceUnits v),
    unitsEquiv v (sourceAction v γ u) =
      ((S01 (I := I)).unitsAction v)
        (middleEval (I := I) v (groupEquiv γ)) (unitsEquiv v u)

attribute [instance] S1399PaperOxGModule.commGroupSourceUnits

/-- Actual S1388 pair datum on the actual middle strip. -/
noncomputable abbrev S1399ActualPairDatum :
    KappaOrbitUnitsActionPairDatum (MiddleGraph (I := I))
      (S00 (I := I)) (S11 (I := I)) :=
  actualMiddlePairDatum (I := I)

theorem S1399ActualPairDatum_sourceUnits (v : V) :
    (S1399ActualPairDatum I).sourceUnits v =
      ((S01 (I := I)).Mon v)ˣ := rfl

theorem S1399ActualPairDatum_kappaUpper_link (v : V) :
    (S1399ActualPairDatum I).kappaUpper v =
      middleKappaUpper (I := I) v := rfl

theorem S1399ActualPairDatum_kappaLower_link (v : V) :
    (S1399ActualPairDatum I).kappaLower v =
      middleKappaLower (I := I) v := rfl

#check S1399PaperOxGModule
#check S1399ActualPairDatum
#check S1399ActualPairDatum_sourceUnits
#check S1399ActualPairDatum_kappaUpper_link
#check S1399ActualPairDatum_kappaLower_link
#check S01_ne_S00
#check S01_ne_S11

end LeanFormal.IUT.XiFPaper.S1399KappaOxGActual

end