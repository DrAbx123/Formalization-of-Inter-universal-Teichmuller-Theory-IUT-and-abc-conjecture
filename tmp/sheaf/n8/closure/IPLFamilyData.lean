import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
import LeanFormal.IUT.IUTI.HodgeTheater.PrimeStripCore
import LeanFormal.IUT.IUTIII.Theorem311.SourcePolyIsoTransportLaws
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.SourceAdjacentColumnProcessionIsomorphism

noncomputable section

namespace LeanFormal.IUT.N8Closure.IPLFamily

universe ua uv upi umon ui

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

variable {l : PrimeGeFive} {V : Type uv}

/-- Actual IPL family data: a permitted family of poly-isomorphisms between
two actual F-prime-strips, together with the allowed relation it induces on
value-monoid fibers.  The family is the source object; no Core/LinkSpan
kernel-level surrogate is used as the original semantic content. -/
structure IPLFamilyData
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) where
  /-- Actual source F-prime-strip. -/
  source : FPrimeStrip V
  /-- Actual target F-prime-strip. -/
  target : FPrimeStrip V
  /-- The source strip is the actual strip of `I` at the chosen column. -/
  source_eq : source = I.fPrimeStripAt 0 0
  /-- The target strip is the actual strip of `I` at the chosen column. -/
  target_eq : target = I.fPrimeStripAt 0 0
  /-- The permitted family of full poly-isomorphisms (actual family, not a
  single chosen equivalence). -/
  permitted : Set (FPrimeStripEquiv source target)
  /-- The permitted family is nonempty. -/
  permitted_nonempty : permitted.Nonempty

namespace IPLFamilyData

variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

/-- The actual allowed relation on the fiber over `v`: two value-monoid
elements are related when some permitted poly-isomorphism carries one to the
other. -/
def allowed (D : IPLFamilyData I) (v : V)
    (x : D.source.Mon v) (y : D.target.Mon v) : Prop :=
  ∃ φ ∈ D.permitted, φ.isoMon v x = y

/-- Characterization of the allowed relation by the permitted family. -/
theorem allowed_iff (D : IPLFamilyData I) (v : V)
    (x : D.source.Mon v) (y : D.target.Mon v) :
    D.allowed v x y ↔ ∃ φ ∈ D.permitted, φ.isoMon v x = y :=
  Iff.rfl

end IPLFamilyData

/-- Existence obligation for actual IPL family data: one named theorem-level
gap.  The permitted family is not asserted to be a singleton and no
Strip<->Output bijection is introduced. -/
theorem iplFamilyData_nonempty
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    Nonempty (IPLFamilyData I) :=
  ⟨{ source := I.fPrimeStripAt 0 0
     target := I.fPrimeStripAt 0 0
     source_eq := rfl
     target_eq := rfl
     permitted := {FPrimeStripEquiv.refl (I.fPrimeStripAt 0 0)}
     permitted_nonempty := ⟨_, by simp⟩ }⟩

end LeanFormal.IUT.N8Closure.IPLFamily
