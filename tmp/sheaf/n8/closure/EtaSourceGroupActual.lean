import tmp.sheaf.n8.closure.EtaSourceActionCarrierCorrected
import Mathlib

/-!
# Actual source action group from LGP/procession data

The source action group is the additive group Label of an actual
SourceLGPProcession, acting on the procession carrier Choice through the
actual ind1/ind2 maps.  It is not the field multiplicative group K^.

The group and its action laws are actual conditional on the LGP procession.
The exact gap is a native N8NativeInput -> SourceLGPProcession construction;
no arbitrary group is introduced.
-/

noncomputable section

namespace ABCBridge.N8.EtaSourceGroupActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.EtaSourceActionCarrierCorrected
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SourceHodgeTheaterBridge

universe ua uv upi umon ui u v w

variable {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
  [AddGroup Label] [Preorder Choice]

/-- Actual source action group from an LGP procession: the group is Label and
the action is ind1/ind2 on the procession carrier. -/
structure EtaSourceGroupActual (P : SourceLGPProcession l Label Choice) where
  action1 : Label → Choice → Choice
  action1_eq : action1 = P.ind1
  action2 : Label → Choice → Choice
  action2_eq : action2 = P.ind2

/-- Actual source group/action from the LGP procession, zero sorry. -/
noncomputable def etaSourceGroupActual (P : SourceLGPProcession l Label Choice) :
    EtaSourceGroupActual P where
  action1 := P.ind1
  action1_eq := rfl
  action2 := P.ind2
  action2_eq := rfl

/-- Actual action laws for the source additive group Label on the procession
carrier. -/
theorem etaSourceGroupActual_laws (P : SourceLGPProcession l Label Choice) :
    (∀ c : Choice, (etaSourceGroupActual P).action1 0 c = c) ∧
      (∀ (g h : Label) (c : Choice),
        (etaSourceGroupActual P).action1 (g + h) c =
          (etaSourceGroupActual P).action1 h ((etaSourceGroupActual P).action1 g c)) ∧
      (∀ c : Choice, (etaSourceGroupActual P).action2 0 c = c) ∧
      (∀ (g h : Label) (c : Choice),
        (etaSourceGroupActual P).action2 (g + h) c =
          (etaSourceGroupActual P).action2 h ((etaSourceGroupActual P).action2 g c)) :=
  ⟨P.ind1_zero, fun g h c => P.ind1_add g h c,
   P.ind2_zero, fun g h c => P.ind2_add g h c⟩

/-- Actual action identification: the source group acts by the LGP ind1/ind2
maps, not by field multiplication. -/
theorem etaSourceGroupActual_action_apply (P : SourceLGPProcession l Label Choice)
    (g : Label) (c : Choice) :
    (etaSourceGroupActual P).action1 g c = P.ind1 g c ∧
      (etaSourceGroupActual P).action2 g c = P.ind2 g c :=
  ⟨rfl, rfl⟩

/-- Exact gap: no actual SourceLGPProcession is constructed from a native
N8NativeInput.  The canonical construction requires SourceDefinition31Data,
which the native root does not supply. -/
def SourceGroupNativeLGPProcessionGap : Prop :=
  ∀ (X : N8NativeInput l), Nonempty (SourceDefinition31Data.{u} l)

end ABCBridge.N8.EtaSourceGroupActual
