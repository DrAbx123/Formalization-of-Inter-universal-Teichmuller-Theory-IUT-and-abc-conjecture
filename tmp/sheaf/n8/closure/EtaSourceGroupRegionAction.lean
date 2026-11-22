import tmp.sheaf.n8.closure.EtaSourceGroupActual
import tmp.sheaf.n8.closure.SourceWitnessedOutput
import Mathlib

/-!
# LGP source-group action on regions, and the source-carrier gap

The actual LGP additive group Label acts on its procession carrier Choice via
ind1/ind2.  This file constructs the induced actual action on regions
Set Choice, with zero and add laws and nonempty-image movement.

The source region of C4 lives in the function-valued ThetaPilotPoint carrier,
while the LGP carrier Choice is an abstract Preorder type.  No production map
Choice -> ThetaPilotPoint exists; this is recorded as the exact carrier gap.
No field multiplication or arbitrary carrier map is used.
-/

noncomputable section

namespace ABCBridge.N8.EtaSourceGroupRegionAction

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SourceHodgeTheaterBridge

universe ua uv upi umon ui u v w

variable {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
  [AddGroup Label] [Preorder Choice]

/-- The actual LGP action on regions of the procession carrier. -/
def lgpRegionAct (P : SourceLGPProcession l Label Choice) (g : Label)
    (S : Set Choice) : Set Choice :=
  P.ind1 g '' S

/-- Zero acts trivially on regions. -/
theorem lgpRegionAct_zero (P : SourceLGPProcession l Label Choice) (S : Set Choice) :
    lgpRegionAct P 0 S = S := by
  ext c
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [P.ind1_zero] using hx
  · intro hc
    exact ⟨c, hc, by simpa using P.ind1_zero c⟩

/-- The region action satisfies the LGP composability law. -/
theorem lgpRegionAct_add (P : SourceLGPProcession l Label Choice)
    (g h : Label) (S : Set Choice) :
    lgpRegionAct P (g + h) S = lgpRegionAct P h (lgpRegionAct P g S) := by
  ext c
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨P.ind1 g x, ⟨x, hx, rfl⟩, ?_⟩
    exact (P.ind1_add g h x).symm
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, P.ind1_add g h x⟩

/-- Nonempty regions remain nonempty under the LGP region action. -/
theorem lgpRegionAct_nonempty (P : SourceLGPProcession l Label Choice)
    (g : Label) {S : Set Choice} (hS : S.Nonempty) :
    (lgpRegionAct P g S).Nonempty := by
  obtain ⟨x, hx⟩ := hS
  exact ⟨P.ind1 g x, ⟨x, hx, rfl⟩⟩

/-- Exact carrier gap: a map from the LGP Choice carrier to the source
function-valued ThetaPilotPoint carrier.  No production map exists; this is the
missing bridge between the LGP region action and C4.U/ThetaPilot regions. -/
structure LGPChoiceToThetaPilot (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (v : V) where
  toPoint : Choice → I.ThetaPilotPoint v

/-- Exact gap proposition: no production LGP Choice -> ThetaPilotPoint carrier
map is available.  This is a carrier gap, not an arbitrary map. -/
def LGPChoiceToThetaPilotGap
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (v : V) : Prop :=
  Nonempty (LGPChoiceToThetaPilot (I := I) (Choice := Choice) v)

end ABCBridge.N8.EtaSourceGroupRegionAction
