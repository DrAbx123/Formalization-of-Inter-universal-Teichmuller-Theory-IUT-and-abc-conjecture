import tmp.sheaf.n8.closure.NativeC1
import tmp.sheaf.n8.closure.C1QuotientFiberData
import tmp.sheaf.n8.closure.SourceInputBinding

/-!
# C1 actual source input: native place slice and target correction

Decision: the old arbitrary SourceInputBinding target (OriginalInput over an
arbitrary V, full-unit fiberMonEquiv) is withdrawn as the C1 target.

Reasons:
1. C1 full-unit fiberMonEquiv is not satisfiable on actual unit monoids
   (order two -1 vs torsion-free value groups).
2. Native source data SourceNativeInitialThetaData supplies native places, not
   an arbitrary old OriginalInput V; no production native -> OriginalInput
   bridge exists.
3. The V=Unit/q=1 sourceHaarActualOriginalInput special case requires
   Unit ~ NumberFieldPlaceIndex; Unit is a subsingleton and the place index is
   nontrivial, so the old SourceInputBinding cannot be formed there.

Actual corrected target:
- NativeActualC1PlaceData: actual native place bijection, selected bad place,
  membership and comap; zero sorry.
- CorrectedC1ActualSourceInput: native place data + actual
  C1PlaceQuotientFiberData (quotient-by-kernel value group target).
- actual constructors below.

Remaining source gaps (named elsewhere): actual SourceImageRealization for the
selected native place, and old-strip-to-PlaceUnitMonoid identification for
literal old Mon quotients.  No arbitrary V or equivalence is introduced.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C1ActualSourceInput

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.N8Closure.C1QuotientFiberData
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

universe ua uv upi umon ui

variable {l : PrimeGeFive}

structure NativeActualC1PlaceData (X : N8NativeInput l) where
  placeEquiv : NativePlaces X.S ≃
    NumberFieldPlaceIndex (F := X.S.arithmetic.Fmod)
  selected : NativePlaces X.S
  selected_mem : selected.1 ∈ X.S.tuple.source.V
  selected_comap :
    NumberFieldPlace.comap (k := X.S.arithmetic.Fmod) selected.1 =
      NumberFieldPlace.finite (badBasePlace X)

noncomputable def nativeActualC1PlaceData (X : N8NativeInput l) :
    NativeActualC1PlaceData X where
  placeEquiv := nativePlaceIndexEquiv X
  selected := badPlace X
  selected_mem := (badPlace X).2
  selected_comap := badPlace_comap X

structure CorrectedC1ActualSourceInput (X : N8NativeInput l) where
  placeData : NativeActualC1PlaceData X
  quotientTarget : C1PlaceQuotientFiberData (F := X.S.arithmetic.Fmod)
  quotientTarget_eq : quotientTarget =
    c1PlaceQuotientFiberData (F := X.S.arithmetic.Fmod)

noncomputable def correctedC1ActualSourceInput (X : N8NativeInput l) :
    CorrectedC1ActualSourceInput X where
  placeData := nativeActualC1PlaceData X
  quotientTarget := c1PlaceQuotientFiberData (F := X.S.arithmetic.Fmod)
  quotientTarget_eq := rfl

theorem no_sourceInputBinding_unit_of_nontrivial_placeIndex
    (I : OriginalInput.{ua, 0, upi, umon, ui} l Unit)
    [Nontrivial (NumberFieldPlaceIndex (F := I.initial.arithmetic.Fmod))] :
    IsEmpty (SourceInputBinding I) := by
  refine ⟨fun O => ?_⟩
  let e := O.place.placeEquiv
  have hsub : Subsingleton
      (NumberFieldPlaceIndex (F := I.initial.arithmetic.Fmod)) :=
    ⟨fun a b => e.symm.injective (Subsingleton.elim (e.symm a) (e.symm b))⟩
  letI : Subsingleton
      (NumberFieldPlaceIndex (F := I.initial.arithmetic.Fmod)) := hsub
  obtain ⟨a, b, hab⟩ := (inferInstance :
    Nontrivial (NumberFieldPlaceIndex (F := I.initial.arithmetic.Fmod))).exists_pair_ne
  exact hab (Subsingleton.elim a b)

theorem correctedC1ActualSourceInput_nonempty (X : N8NativeInput l) :
    Nonempty (CorrectedC1ActualSourceInput X) :=
  ⟨correctedC1ActualSourceInput X⟩

end LeanFormal.IUT.N8Closure.C1ActualSourceInput
