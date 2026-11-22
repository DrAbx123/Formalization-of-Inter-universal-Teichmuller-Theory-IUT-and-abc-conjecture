import Mathlib.CategoryTheory.Galois.Examples
import Mathlib.CategoryTheory.Galois.IsFundamentalgroup
import Mathlib.CategoryTheory.Action.Continuous
import Mathlib.Topology.Category.FinTopCat
import Iut.Foundations.SourceContinuousAnabelioid
import Iut.Foundations.Orbicurve

noncomputable section
open CategoryTheory
open scoped FintypeCatDiscrete

namespace S1737Probe

variable (F : Type) [Field F]

example : PreGaloisCategory.IsFundamentalGroup
    (Iut.continuousActionFiber (Iut.AbsoluteGaloisProfinite F))
    (Iut.AbsoluteGaloisProfinite F) :=
  Iut.continuousAction_isFundamentalGroup _

def AllFiniteActionsContinuous (G : Type) [Group G] [TopologicalSpace G] : Prop :=
  ∀ X : Action FintypeCat.{0} G, Action.IsContinuous X

def AbsoluteGaloisActionForgetMissing : Prop :=
  AllFiniteActionsContinuous (Iut.AbsoluteGaloisProfinite F)

instance actionForgetMulAction (G : Type) [Group G] (X : Action FintypeCat.{0} G) :
    MulAction G ((Action.forget FintypeCat.{0} G).obj X).obj :=
  inferInstanceAs (MulAction G X.V)

instance actionForgetIsNaturalSMul (G : Type) [Group G] :
    PreGaloisCategory.IsNaturalSMul (Action.forget FintypeCat.{0} G) G where
  naturality g {X Y} f x := by
    change f.hom ((X.ρ g).hom x) = (Y.ρ g).hom (f.hom x)
    exact ConcreteCategory.congr_hom (f.comm g) x

theorem actionForget_isFundamentalGroup_of_allContinuous
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hcont : AllFiniteActionsContinuous G) :
    PreGaloisCategory.IsFundamentalGroup (Action.forget FintypeCat.{0} G) G where
  naturality := actionForgetIsNaturalSMul G |>.naturality
  transitive_of_isGalois X := by
    intro hGalois
    letI := hGalois
    exact FintypeCat.Action.pretransitive_of_isConnected G X
  continuous_smul X := hcont X
  non_trivial' g h :=
    Iut.continuousAction_nontrivial G g (fun X x => h X.obj x)

theorem absoluteGalois_actionForget_isFundamentalGroup_of_allContinuous
    (h : AbsoluteGaloisActionForgetMissing F) :
    PreGaloisCategory.IsFundamentalGroup
      (Action.forget FintypeCat.{0} (Iut.AbsoluteGaloisProfinite F))
      (Iut.AbsoluteGaloisProfinite F) :=
  actionForget_isFundamentalGroup_of_allContinuous _ h

end S1737Probe
