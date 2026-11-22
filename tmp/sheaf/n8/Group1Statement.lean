/-
N8 group 1 -- stage 2: the global Example 3.6(ii) Frobenioid at the arithmetic
base field of a Theorem 3.11 input.

Source: tmp/sheaf/n8/group1-STAGE1.md §7.2 and §9.  Paper anchor: IUT III,
Example 3.6(ii) (III p.107), packaged through Frobenioids I, Theorem 5.2(ii)
and Definition 1.3.

This is a standalone trial file: no production edit.  The four declarations
below are exactly the ones fixed in §7.2.  Both prerequisite facts about the
one-object/one-arrow base category are proved, so no sorry is used.
-/
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceModelBackend
import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
import Iut.Foundations.SourceModelFrobenioidPresentation

namespace LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceModelBackend

open CategoryTheory

universe u

/-- The one-object/one-arrow base category of Example 3.6 is connected. -/
instance bottomBase_isConnected :
    CategoryTheory.IsConnected (SourceModelBackend.BottomBase) := by
  haveI : Nonempty BottomBase := ⟨bottomPoint⟩
  haveI : Subsingleton BottomBase := inferInstance
  exact CategoryTheory.isConnected_of_nonempty_and_subsingleton

/-- Every arrow of the one-arrow base category is an epimorphism. -/
theorem bottomBase_arrow_epi
    {X Y : SourceModelBackend.BottomBase} (f : X ⟶ Y) : Epi f := by
  obtain rfl : X = Y := Subsingleton.elim X Y
  rw [bottomBase_hom_eq_id f]
  infer_instance

/-- Frobenioids I, Theorem 5.2(ii), at the actual place data of `F`; the
divisor monoid is the effective cone of `F` and the rational functions are
`Additive F^×` (Example 3.6, (ii)). -/
noncomputable def numberFieldFrobenioidPresentation
    (F : Type u) [Field F] [NumberField F] :
    Iut.FrobenioidPresentation :=
  Iut.SourceModelFrobenioid.Carrier.frobenioidPresentation
    (D := BottomBase) (IsFSM := BottomFSM)
    (Phi := globalDivisorMonoidOn (F := F))
    (data := numberFieldSourceModelInput (F := F))
    (fun f => bottomBase_arrow_epi f)

end LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceModelBackend

namespace LeanFormal.IUT.Theorem311Source

universe ua uv upi umon ui

/-- The global Frobenioid of IUT III, Example 3.6, (ii) attached to the
arithmetic base field `F_mod` of a Theorem 3.11 input. -/
noncomputable def sourceOriginalInputFrobenioidPresentation
    {l : PrimeGeFive} {V : Type uv}
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    Iut.FrobenioidPresentation :=
  LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceModelBackend.numberFieldFrobenioidPresentation
    (F := I.initial.arithmetic.Fmod)

end LeanFormal.IUT.Theorem311Source
