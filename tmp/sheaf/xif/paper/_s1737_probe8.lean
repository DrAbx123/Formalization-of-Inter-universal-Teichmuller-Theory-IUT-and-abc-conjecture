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

variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

instance actionForgetMulAction (X : Action FintypeCat.{0} G) :
    MulAction G ((Action.forget FintypeCat.{0} G).obj X).obj :=
  inferInstanceAs (MulAction G X.V)

instance actionForgetIsNaturalSMul :
    PreGaloisCategory.IsNaturalSMul (Action.forget FintypeCat.{0} G) G where
  naturality g {X Y} f x := by
    change f.hom ((X.ρ g).hom x) = (Y.ρ g).hom (f.hom x)
    exact ConcreteCategory.congr_hom (f.comm g) x

def AllFiniteActionsContinuous : Prop :=
  ∀ X : Action FintypeCat.{0} G, Action.IsContinuous X

variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

theorem actionForget_isFundamentalGroup_of_allContinuous
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

theorem allContinuous_of_isFundamentalGroup
    (h : PreGaloisCategory.IsFundamentalGroup (Action.forget FintypeCat.{0} G) G) :
    AllFiniteActionsContinuous G := by
  intro X
  exact h.continuous_smul X

theorem actionForget_isFundamentalGroup_iff_allContinuous :
    PreGaloisCategory.IsFundamentalGroup (Action.forget FintypeCat.{0} G) G ↔
      AllFiniteActionsContinuous G :=
  ⟨allContinuous_of_isFundamentalGroup G, actionForget_isFundamentalGroup_of_allContinuous G⟩

variable {G}

noncomputable def continuousEtaleFundamentalGroup (G : ProfiniteGrp.{0}) :
    Iut.EtaleFundamentalGroup where
  Cover := ContAction FintypeCat.{0} G
  coverCategory := inferInstance
  galoisCategory := Iut.continuousAction_galoisCategory G
  fiber := Iut.continuousActionFiber G
  fiberFunctor := Iut.continuousAction_fiberFunctor G
  group := G
  action := Iut.continuousActionFiber_mulAction G
  isFundamentalGroup := Iut.continuousAction_isFundamentalGroup G

theorem continuousEtaleFundamentalGroup_certified (G : ProfiniteGrp.{0}) :
    letI := (continuousEtaleFundamentalGroup G).coverCategory
    letI := (continuousEtaleFundamentalGroup G).galoisCategory
    letI := (continuousEtaleFundamentalGroup G).fiberFunctor
    letI (X : (continuousEtaleFundamentalGroup G).Cover) :=
      (continuousEtaleFundamentalGroup G).action X
    PreGaloisCategory.IsFundamentalGroup (continuousEtaleFundamentalGroup G).fiber G :=
  (continuousEtaleFundamentalGroup G).isFundamentalGroup

end S1737Probe
