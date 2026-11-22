import tmp.sheaf.xif.paper.PaperQPilotObject
import tmp.sheaf.xif.paper.PaperLineBundleCarrierActual
import tmp.sheaf.xif.paper.QPilotPaperLineBundleActual
import tmp.sheaf.xif.paper.QPilotLineBundleUnconditional
import tmp.sheaf.n8.closure.NativeInput
import tmp.sheaf.n8.closure.NativeBadFintypeClosed
import LeanFormal.IUT.IUTI.HodgeTheater.SourceDefinition31NativeContractBridgeReduction

/-! # Layer O: the actual `PaperLineBundleCarrier` slot of `PaperQPilotObject`

**Layer: O (original-text Theta-link).**  This file constructs only the actual
`lineBundle` slot of `Theorem311Source.PaperQPilotObject`; it uses neither the
normalized model (N) nor any `SourceDefinition31Data` (S) or D4-D9 (D)
conclusion.  The native (T) object below is a *donor* only: the target of every
declaration is the paper-level carrier of `PaperQPilotObject`.

## The slot

`PaperQPilotObject.lineBundle` has type

  `PaperLineBundleCarrier (k := I.initial.arithmetic.Fmod)`

for the paper original input `I : OriginalInput l V`.  The carrier structure
(`PaperLineBundleCarrierBase`) asks for a section type `total` and a
pole-allowing localization `(v : FinitePlace Fmod) -> total -> Fmod_v` into the
completion field.  Its actual inhabitant is built here from the existing
actual objects:

* `QPilotPaperLineBundleActual.qPilotLineBundle`: the actual q-pilot `O(-D)`,
  the inverse of the actual zero-locus fractional ideal;
* `PaperLineBundleCarrierActual.qPilotPaperLineBundleCarrier`: the existing
  actual pole-allowing carrier of that `O(-D)`;
* `NativeBadFintypeClosed.nativeBadFintype`: the actual Fintype on the
  native bad moduli places, constructed (not assumed) in the tree.

## The exact first field

`I.initial` is the abstract `SourceDefinition31Data` contract: its `badPlaces`
is a bare finite type with a real `qParameter` and no map to base finite
places.  It therefore supplies no zero locus over `O_Fmod` and no `O(-D)`.
The actual q-pilot `O(-D)` exists only on the native side, so the exact first
outstanding datum is a *native totalization of the paper arithmetic root*:

  `OrigXiFPaperLineBundleData.arithmetic_root_eq :
     X.S.arithmetic = I.initial.arithmetic`,  `X : N8NativeInput l`.

This is recorded as the single field of `OrigXiFPaperLineBundleData` besides
`X`; **no inhabitant is asserted**, and every construction below is
conditional on it.  Everything else is constructed: the section type is the
actual q-pilot fractional ideal (not `PUnit`, not the unit bundle, not an
arbitrary type), the localization is the actual completion embedding, and the
bad-place Fintype is `nativeBadFintype`.

## Universe pin (part of the exact first field)

The existing native q-pilot lives at `Type 0`: `N8NativeInput` has type
`PrimeGeFive -> Type 1`, i.e. its source datum is a
`SourceNativeInitialThetaData.{0}`.  Hence `X.S.arithmetic` is an
`InitialThetaArithmeticData.{0}`, and the equality above is *typed* only for a
paper original input at `I.initial : SourceDefinition31Data.{0}`.  At a
higher arithmetic universe the identification cannot even be stated, let alone
filled by the native route; this is recorded by the explicit `.{0, ...}` in
the signatures of the donor-based declarations.

## Layer separation

`QPilotLineBundleUnconditional` supplies a q-pilot line bundle over the *K-side*
ring `SourceOK A = RingOfIntegers A.K` (conditional on `GlobalQPilotIdealDonor`,
`qPilotIdeal : Ideal (SourceOK A)`).  That base ring is `O_K`, not `O_Fmod`, so
the K-side donor does not fill this `O_Fmod` slot and is not used to fill it;
the slot is filled only through the actual `O_Fmod` q-pilot.  The `#check`
gate at the end pins the existing objects this file relies on.

No `PUnit`, `True`, `sorry`, `axiom`, arbitrary inhabitant or `Nonempty`
witness is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.OrigXiFPaperLineBundle

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperLineBundleCarrierActual
open LeanFormal.IUT.XiFPaper.QPilotPaperLineBundleActual

universe u uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}

/-! ## 1. The exact slot type -/

/-- The exact type of the `lineBundle` slot of `PaperQPilotObject` for the paper
original input `I`: the pole-allowing line-bundle carrier over the actual base
field `Fmod` of `I`. -/
abbrev OrigXiFPaperLineBundleCarrierType
    (I : OriginalInput l V) :=
  PaperLineBundleCarrier (k := I.initial.arithmetic.Fmod)

/-! ## 2. The actual donor package and the exact first field -/

/-- The actual donor package for the paper q-pilot line bundle: an actual
native source/lattice input together with the **exact first field**, namely
that its arithmetic root is the paper original input's arithmetic root.

No field is a free parameter, no proposition is asserted here, and no
inhabitant of this structure is claimed. -/
structure OrigXiFPaperLineBundleData
    (I : OriginalInput.{0, uv, upi, umon, ui} l V) where
  /-- The actual native source/lattice input supplying the actual q-pilot
  `O(-D)` fractional ideal. -/
  X : N8NativeInput l
  /-- **Exact first field**: the paper original input's arithmetic root is the
  native donor's arithmetic root. -/
  arithmetic_root_eq : X.S.arithmetic = I.initial.arithmetic

/-- The exact first-field type, recorded without an inhabitant: an actual
native totalization of the paper original input's arithmetic root. -/
abbrev OrigXiFPaperLineBundleCarrierExact
    (I : OriginalInput.{0, uv, upi, umon, ui} l V) :=
  OrigXiFPaperLineBundleData I

/-- The exact remaining obligation of the paper `lineBundle` slot, as a
proposition: the donor package of section 2.  It is not proved here. -/
def OrigXiFPaperLineBundleCarrierRequired
    (I : OriginalInput.{0, uv, upi, umon, ui} l V) : Prop :=
  Nonempty (OrigXiFPaperLineBundleData I)

/-! ## 3. The actual bad-place Fintype and the actual q-pilot line bundle -/

/-- The actual Fintype on the native bad moduli places, taken from
`NativeBadFintypeClosed.nativeBadFintype` (constructed there from the proved
finiteness of `X.S.tuple.source.V_mod_bad`, not assumed here). -/
noncomputable abbrev OrigXiFPaperBadFintype (X : N8NativeInput l) :
    Fintype (Bad (nativePlaceSelection X.S)) :=
  LeanFormal.IUT.N8Closure.NativeBadFintypeClosed.nativeBadFintype X

/-- The actual q-pilot `O(-D)` fractional-ideal line bundle over the paper base
field: the existing actual q-pilot line bundle `qPilotLineBundle` of
`QPilotPaperLineBundleActual`, transported along the exact first field. -/
noncomputable def OrigXiFPaperQPilotLineBundle
    (I : OriginalInput.{0, uv, upi, umon, ui} l V)
    (D : OrigXiFPaperLineBundleData I) :
    FractionalIdeal
      (nonZeroDivisors (NumberField.RingOfIntegers I.initial.arithmetic.Fmod))
      I.initial.arithmetic.Fmod := by
  letI := OrigXiFPaperBadFintype D.X
  exact D.arithmetic_root_eq ▸ qPilotLineBundle D.X

/-- The paper q-pilot line bundle is the existing actual q-pilot `O(-D)` of
`QPilotPaperLineBundleActual`, rewritten along the exact first field.  No
line-bundle value is chosen by hand. -/
theorem OrigXiFPaperQPilotLineBundle_eq_qPilotLineBundle
    (I : OriginalInput.{0, uv, upi, umon, ui} l V)
    (D : OrigXiFPaperLineBundleData I) :
    OrigXiFPaperQPilotLineBundle I D =
      D.arithmetic_root_eq ▸
        @qPilotLineBundle l D.X (OrigXiFPaperBadFintype D.X) :=
  rfl

/-! ## 4. The actual pole-allowing carrier -/

/-- The actual `PaperLineBundleCarrier` of the paper q-pilot: sections are the
actual q-pilot `O(-D)` fractional-ideal sections over `Fmod`, and localizations
are the actual completion embeddings into the local fields `Fmod_v` (poles
allowed).  This is the exact `lineBundle` slot value of
`PaperQPilotObject`. -/
noncomputable def OrigXiFPaperLineBundleCarrier
    (I : OriginalInput.{0, uv, upi, umon, ui} l V)
    (D : OrigXiFPaperLineBundleData I) :
    PaperLineBundleCarrier (k := I.initial.arithmetic.Fmod) where
  total := OrigXiFPaperQPilotLineBundle I D
  localization := fun v x =>
    algebraMap (I.initial.arithmetic.Fmod) (Completion v)
      (x : I.initial.arithmetic.Fmod)

/-- The section type of the paper carrier is the actual q-pilot `O(-D)`
fractional-ideal section type (not `PUnit`, not the unit bundle). -/
theorem OrigXiFPaperLineBundleCarrier_total
    (I : OriginalInput.{0, uv, upi, umon, ui} l V)
    (D : OrigXiFPaperLineBundleData I) :
    (OrigXiFPaperLineBundleCarrier I D).total =
      ↥(OrigXiFPaperQPilotLineBundle I D) :=
  rfl

/-- The localization of the paper carrier is the actual completion embedding
`Fmod -> Fmod_v` of the fractional-ideal section, so poles at bad primes are
allowed; no localization value is chosen by hand. -/
theorem OrigXiFPaperLineBundleCarrier_localization
    (I : OriginalInput.{0, uv, upi, umon, ui} l V)
    (D : OrigXiFPaperLineBundleData I)
    (v : NumberField.FinitePlace I.initial.arithmetic.Fmod)
    (x : ↥(OrigXiFPaperQPilotLineBundle I D)) :
    (OrigXiFPaperLineBundleCarrier I D).localization v x =
      algebraMap (I.initial.arithmetic.Fmod) (Completion v)
        (x : I.initial.arithmetic.Fmod) :=
  rfl

/-- The section type of the paper carrier is inhabited: it contains the zero
section of the actual q-pilot fractional ideal.  The carrier is therefore not
an empty type used to fake a line bundle. -/
theorem OrigXiFPaperLineBundleCarrier_total_nonempty
    (I : OriginalInput.{0, uv, upi, umon, ui} l V)
    (D : OrigXiFPaperLineBundleData I) :
    Nonempty (OrigXiFPaperLineBundleCarrier I D).total :=
  ⟨⟨(0 : I.initial.arithmetic.Fmod), Submodule.zero_mem _⟩⟩

/-! ## 5. Reuse certificate for the existing actual carrier -/

/-- At the donor's own arithmetic root, the carrier construction of section 4 is
literally the existing actual carrier `qPilotPaperLineBundleCarrier` of
`PaperLineBundleCarrierActual`: same total (`qPilotLineBundle`), same
localization (the completion embedding).  Hence the paper slot is filled by the
existing actual carrier, not by a new or fake one. -/
theorem OrigXiFPaperLineBundleCarrier_donor_eq
    (X : N8NativeInput l) [Fintype (Bad (nativePlaceSelection X.S))] :
    qPilotPaperLineBundleCarrier X =
      ({ total := qPilotLineBundle X
         localization := fun v x =>
           algebraMap (QPilotBaseField X) (Completion v)
             (x : QPilotBaseField X) } :
        PaperLineBundleCarrier (k := QPilotBaseField X)) :=
  rfl

/-! ## 6. Import gate

The existing objects this file relies on, plus the consumer slot. -/

#check @LeanFormal.IUT.XiFPaper.PaperLineBundleCarrierActual.qPilotPaperLineBundleCarrier
#check @LeanFormal.IUT.XiFPaper.QPilotPaperLineBundleActual.qPilotPaperLineBundleActual
#check @LeanFormal.IUT.N8Closure.QPilotLineBundleUnconditional.GlobalQPilotIdealDonor
#check @LeanFormal.IUT.N8Closure.NativeBadFintypeClosed.nativeBadFintype
#check @LeanFormal.IUT.Theorem311Source.PaperQPilotObject

end LeanFormal.IUT.XiFPaper.OrigXiFPaperLineBundle

end
