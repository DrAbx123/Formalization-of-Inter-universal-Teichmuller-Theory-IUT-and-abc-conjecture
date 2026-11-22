import tmp.sheaf.xif.paper.GlobalIQHullInterfaceActualAdapted
import tmp.sheaf.xif.paper.ThetaPilotObjectActual

/-!
# Global Theta-pilot image/hull candidates

The per-place actual Theta-pilot image and holomorphic hull are

  I.possibleThetaPilotImageSet v R n : Set (I.ThetaPilotPoint v)
  I.sourceHolomorphicHull v R n      : Set (I.ThetaPilotPoint v)

with the actual containment image subset hull.  Taking the global product over
all places gives actual global candidates

  GlobalThetaPilotCarrier := (v : V) -> I.ThetaPilotPoint v
  globalThetaPilotImageSet R n := {x | forall v, x v in possible image}
  globalThetaPilotHull R n     := {x | forall v, x v in source hull}

and the actual containment/nonemptiness proofs.

What is not supplied is an actual map from this global Theta-pilot carrier into
the global IQ tensor ambient LiteralIQAmbient, and the lambda-scaling/Ind data on
the global carrier.  Those are recorded as exact obstruction data; the image and
hull themselves are not fabricated inside the IQ ambient.

No PUnit/True, arbitrary data, axiom or sorry is used.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

namespace LeanFormal.IUT.XiFPaper.GlobalIQHullThetaPilotActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.ThetaPilotObjectActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

/-- The global Theta-pilot product carrier. -/
abbrev GlobalThetaPilotCarrier : Type _ :=
  (v : V) → I.ThetaPilotPoint v

/-- Global Theta-pilot image set: points whose every place lies in the actual
per-place possible image set. -/
def globalThetaPilotImageSet
    (R : ∀ v : V, I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    Set (GlobalThetaPilotCarrier (I := I)) :=
  {x | ∀ v : V, x v ∈ I.possibleThetaPilotImageSet v (R v) n}

/-- Global Theta-pilot holomorphic hull: points whose every place lies in the
actual per-place source holomorphic hull. -/
def globalThetaPilotHull
    (R : ∀ v : V, I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    Set (GlobalThetaPilotCarrier (I := I)) :=
  {x | ∀ v : V, x v ∈ I.sourceHolomorphicHull v (R v) n}

/-- The actual global image set is contained in the actual global hull. -/
theorem globalThetaPilotImageSet_subset_hull
    (R : ∀ v : V, I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    globalThetaPilotImageSet (I := I) R n ⊆
      globalThetaPilotHull (I := I) R n := by
  intro x hx v
  exact I.possibleThetaPilotImage_subset_sourceHolomorphicHull
    v (R v) n (hx v)

/-- An actual global point in the image/hull, chosen from the nonempty
per-place possible image sets. -/
noncomputable def globalThetaPilotPoint
    (R : ∀ v : V, I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    GlobalThetaPilotCarrier (I := I) :=
  fun v => Classical.choice
    (I.possibleThetaPilotImageSet_nonempty v (R v) n)

/-- The chosen global point lies in the actual global image set. -/
theorem globalThetaPilotPoint_mem_imageSet
    (R : ∀ v : V, I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    globalThetaPilotPoint (I := I) R n ∈
      globalThetaPilotImageSet (I := I) R n := by
  intro v
  exact Classical.choice_spec
    (I.possibleThetaPilotImageSet_nonempty v (R v) n)

/-- The actual global image set is nonempty. -/
theorem globalThetaPilotImageSet_nonempty
    (R : ∀ v : V, I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    (globalThetaPilotImageSet (I := I) R n).Nonempty :=
  ⟨globalThetaPilotPoint (I := I) R n,
    globalThetaPilotPoint_mem_imageSet (I := I) R n⟩

/-- The actual global hull is nonempty. -/
theorem globalThetaPilotHull_nonempty
    (R : ∀ v : V, I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    (globalThetaPilotHull (I := I) R n).Nonempty := by
  rcases globalThetaPilotImageSet_nonempty (I := I) R n with ⟨x, hx⟩
  exact ⟨x, globalThetaPilotImageSet_subset_hull (I := I) R n hx⟩

/-- Actual global Theta-pilot image/hull candidate data. -/
structure GlobalThetaPilotImageHullActual where
  carrier : Type
  imageSet : Set carrier
  hull : Set carrier
  imageSet_subset_hull : imageSet ⊆ hull
  image_nonempty : imageSet.Nonempty
  hull_nonempty : hull.Nonempty

/-- The actual global image/hull candidate from the per-place source sets. -/
noncomputable def globalThetaPilotImageHullActual
    (R : ∀ v : V, I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    GlobalThetaPilotImageHullActual (I := I) where
  carrier := GlobalThetaPilotCarrier (I := I)
  imageSet := globalThetaPilotImageSet (I := I) R n
  hull := globalThetaPilotHull (I := I) R n
  imageSet_subset_hull := globalThetaPilotImageSet_subset_hull (I := I) R n
  image_nonempty := globalThetaPilotImageSet_nonempty (I := I) R n
  hull_nonempty := globalThetaPilotHull_nonempty (I := I) R n

/-- Exact missing embedding from the global Theta-pilot carrier into the global
IQ tensor ambient, with the image/hull transported. -/
structure GlobalThetaPilotIQEmbedding
    (C3 : SourcePilotRegionData (l := l) (V := V) I) (j : Nat)
    (R : ∀ v : V, I.SourceImageRealization v) (n : ThetaPilotCarrier l) where
  embed : GlobalThetaPilotCarrier (I := I) → GlobalIQAmbient (C3 := C3) j
  imageSetInAmbient : Set (GlobalIQAmbient (C3 := C3) j)
  hullInAmbient : Set (GlobalIQAmbient (C3 := C3) j)
  imageSetInAmbient_eq : imageSetInAmbient =
    embed '' globalThetaPilotImageSet (I := I) R n
  hullInAmbient_eq : hullInAmbient =
    embed '' globalThetaPilotHull (I := I) R n
  imageSetInAmbient_subset_hull : imageSetInAmbient ⊆ hullInAmbient

/-- Exact embedding/scaling obstruction: the global Theta-pilot image/hull
candidate has no actual map into the global IQ tensor ambient. -/
def GlobalThetaPilotIQEmbeddingObstruction
    (C3 : SourcePilotRegionData (l := l) (V := V) I) (j : Nat)
    (R : ∀ v : V, I.SourceImageRealization v) (n : ThetaPilotCarrier l) : Prop :=
  Nonempty (GlobalThetaPilotIQEmbedding (I := I) C3 j R n)

/-- The actual candidate image and hull are the per-place product sets. -/
@[simp] theorem globalThetaPilotImageHullActual_imageSet
    (R : ∀ v : V, I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    (globalThetaPilotImageHullActual (I := I) R n).imageSet =
      globalThetaPilotImageSet (I := I) R n := rfl

/-- The actual candidate hull is the per-place product hull. -/
@[simp] theorem globalThetaPilotImageHullActual_hull
    (R : ∀ v : V, I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    (globalThetaPilotImageHullActual (I := I) R n).hull =
      globalThetaPilotHull (I := I) R n := rfl

end LeanFormal.IUT.XiFPaper.GlobalIQHullThetaPilotActualAdapted

end
