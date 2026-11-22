import tmp.sheaf.xif.paper.S2935HeightLeProcessionActual
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCHeightArithmeticWeightComparison
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2935HeightLeProcessionActual
namespace LeanFormal.IUT.XiFPaper.S2945S2935Equivalence

abbrev S2945AdditiveBound : Prop :=
  ABCHeightWeightAdditiveBoundV2

abbrev S2945Procession (n : Nat) : Prop :=
  S2935HeightLeProcession n

/-- Exact missing direction: additive ABC height bound to the per-triple
J-height/procession bound. -/
def S2945AdditiveToProcessionBridge (n : Nat) : Prop :=
  S2945AdditiveBound → S2945Procession n

/-- Exact missing direction: uniform procession bounds to the additive ABC
height bound. -/
def S2945ProcessionToAdditiveBridge : Prop :=
  (∀ n, S2945Procession n) → S2945AdditiveBound

theorem S2945_additive_to_procession
    (n : Nat) (hbridge : S2945AdditiveToProcessionBridge n)
    (h : S2945AdditiveBound) : S2945Procession n :=
  hbridge h

theorem S2945_procession_to_additive
    (hbridge : S2945ProcessionToAdditiveBridge)
    (h : ∀ n, S2945Procession n) : S2945AdditiveBound :=
  hbridge h

#check S2945AdditiveBound
#check S2945Procession
#check S2945AdditiveToProcessionBridge
#check S2945ProcessionToAdditiveBridge
#check S2945_additive_to_procession
#check S2945_procession_to_additive

end LeanFormal.IUT.XiFPaper.S2945S2935Equivalence