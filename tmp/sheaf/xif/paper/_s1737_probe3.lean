import Mathlib.CategoryTheory.Galois.Examples
import Mathlib.CategoryTheory.Galois.IsFundamentalgroup
import Mathlib.CategoryTheory.Action.Continuous
import Mathlib.Topology.Category.FinTopCat
import Iut.Foundations.SourceContinuousAnabelioid

noncomputable section
open CategoryTheory
open scoped FintypeCatDiscrete

namespace S1737Probe

variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

instance actionForgetMulAction (X : Action FintypeCat.{0} G) :
    MulAction G ((Action.forget FintypeCat.{0} G).obj X).obj :=
  inferInstanceAs (MulAction G X.V)

instance actionForgetIsNaturalSMul :
    PreGaloisCategory.IsNaturalSMul (Action.forget FintypeCat.{0} G) G where
  naturality g {X Y} f x := by
    change f.hom ((X.ρ g).hom x) = (Y.ρ g).hom (f.hom x)
    exact ConcreteCategory.congr_hom (f.comm g) x

variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

theorem actionForget_isFundamentalGroup_of_all_continuous
    (hcont : ∀ X : Action FintypeCat.{0} G, Action.IsContinuous X) :
    PreGaloisCategory.IsFundamentalGroup (Action.forget FintypeCat.{0} G) G where
  naturality := actionForgetIsNaturalSMul G |>.naturality
  transitive_of_isGalois X := by
    intro hGalois
    letI := hGalois
    exact FintypeCat.Action.pretransitive_of_isConnected G X
  continuous_smul X := hcont X
  non_trivial' g h :=
    Iut.continuousAction_nontrivial G g (fun X x => h X.obj x)

end S1737Probe