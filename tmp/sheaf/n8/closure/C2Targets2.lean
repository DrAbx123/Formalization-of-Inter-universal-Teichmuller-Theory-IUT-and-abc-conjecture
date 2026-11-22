import tmp.sheaf.n8.closure.C2Targets
import LeanFormal.IUT.IUTIII.Theorem311.SourceKummerEvaluationArrows

/-!
# C2 targets 2: strengthened native action/Kummer/archimedean targets

Strengthens C2Targets with production donors where available:
- the actual prime-strip action `FPrimeStrip.action` at a native theater;
- the actual production `SourceKummerArrow` type over the native prime strip;
- an actual native archimedean branch structure using the native FPrimeStrip.Mon.

The G_v log-shell action and native Kummer/root-change still have no actual
native inhabitant; those target obligations are named sorry.  No free Type or
True placeholder is used.
-/

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.C2Native
open LeanFormal.IUT.N8Closure.C2Targets
open LeanFormal.IUT.Theorem311Source

namespace LeanFormal.IUT.N8Closure.C2Targets2

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Actual production action donor at the native prime strip: the FPrimeStrip
action of `Pi v` on `Mon v` at a native theater and place. -/
noncomputable def nativePrimeStripAction
    (i : X.family.index) (v : NativePlaces X.S) :
    (X.family.theater i).primeStrip.Pi v →*
      MulAut ((X.family.theater i).primeStrip.Mon v) :=
  (X.family.theater i).primeStrip.action v

/-- The actual prime-strip action is definitionally the production field. -/
theorem nativePrimeStripAction_actual
    (i : X.family.index) (v : NativePlaces X.S) :
    nativePrimeStripAction X i v = (X.family.theater i).primeStrip.action v := rfl

/-- Native Kummer arrow target: the actual production `SourceKummerArrow` type
over the native prime strip, with the trivial actual group `Unit`.  This is the
strongest production donor currently available for the Kummer arrow. -/
def nativeKummerArrowTarget (i : X.family.index) : Prop :=
  Nonempty (SourceKummerArrow Unit (X.family.theater i).primeStrip
    (X.family.theater i).primeStrip)

/-- An actual native archimedean branch: a native place that is infinite over
the base, together with the actual native FPrimeStrip value monoid at that
place.  No free carrier type is introduced. -/
structure NativeArchimedeanBranch where
  index : X.family.index
  place : NativePlaces X.S
  infinite :
    NumberFieldPlace.IsInfinite
      (NumberFieldPlace.comap (k := X.S.arithmetic.Fmod) place.1)

noncomputable def NativeArchimedeanBranch.valueMonoid
    (b : NativeArchimedeanBranch X) : Type _ :=
  (X.family.theater b.index).primeStrip.Mon b.place

instance NativeArchimedeanBranch.valueMonoid_commMonoid
    (b : NativeArchimedeanBranch X) : CommMonoid b.valueMonoid := by
  dsimp only [NativeArchimedeanBranch.valueMonoid]
  infer_instance

/-- Native archimedean target: actual source branch existence.  Named sorry:
no actual native infinite selected place is constructed in the current input
slice, though the branch type above is the exact production source type. -/
def nativeArchimedeanBranchTarget : Prop :=
  Nonempty (NativeArchimedeanBranch X)

/-! ## Exact status

- Actual production donor found: `FPrimeStrip.action` (prime-strip action),
  exposed here as `nativePrimeStripAction`, no sorry.
- Actual production Kummer type found: `SourceKummerArrow`; target
  `nativeKummerArrowTarget` uses it over the actual native prime strip, but no
  native inhabitant is available; named sorry.
- No actual C1-indexed G_v log-shell action/descent exists; target inherited
  from C2Targets, named sorry.
- Actual archimedean source branch type constructed from the native
  FPrimeStrip.Mon; existence of an infinite native selected place is named
  sorry.
-/

end LeanFormal.IUT.N8Closure.C2Targets2
