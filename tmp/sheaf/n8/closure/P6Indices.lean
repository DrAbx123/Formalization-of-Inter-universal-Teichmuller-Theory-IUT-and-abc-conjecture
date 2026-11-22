import tmp.sheaf.n8.closure.NativeC1
import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHull

/-!
# P6 index types: S/L, alpha, R_alpha, and component indices

Paper-facing index discipline for C9/P6.

- `S` is the actual native Definition-3.1 initial data.
- `L` is represented here by the current `NativeLattice S` slice.  The full
  paper log-theta-lattice type is NOT in production; `NativeLattice` is only
  the theater-family slice, so this file records that as an exact statement
  gap and does not pretend it is the full L.
- `IntegerColumnRow = Int × Int` is the theater column/row index `(n,m)`.
- `ProcessionIndex l = ThetaPilotCarrier l = Fin (lStar l.value + 1)` is the
  finite theta-pilot procession index.  It is NOT `Int × Int` and may not be
  substituted for `(n,m)`.
- `SignedLabelIndex l` is the finite label set.
- `PlaceIndex X`, `TupleIndex X`, `AlphaIndex`, `RAlphaIndex` are the exact
  dependency chain for local places, tensor tuples, complete source choices,
  and output-region components.
- `RAlphaFamily` carries the region map `R_alpha`; the output carrier is an
  explicit parameter because no source output-carrier type is yet frozen.

## Exact missing L declaration (statement gap, not added as a fake type)

The production tree has no declaration

  `PaperLogThetaLattice (S : SourceNativeInitialThetaData l) : Type`

with the paper log-theta-lattice fields depending on `S` and `V(S)`.  The
current `L` alias is only `NativeLattice S`, the theater-family slice; it is not
claimed to be the full paper `L`.  A proper declaration must be a dependent
source type, not an arbitrary `Type`, and must not be replaced by a free field.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.P6Indices

universe u v w

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

variable {l : PrimeGeFive}

/-- S: actual native initial Theta data. -/
abbrev S (l : PrimeGeFive) := SourceNativeInitialThetaData l

/-- L: current Lean entry, the native theater-family lattice slice.
Statement gap: the full paper log-theta-lattice type is not in production. -/
abbrev L {l : PrimeGeFive} (S : SourceNativeInitialThetaData l) := NativeLattice S

/-- Integer theater column/row index `(n,m)`. -/
abbrev IntegerColumnRow := Int × Int

/-- Finite theta-pilot procession index `n : ThetaPilotCarrier l`. -/
abbrev ProcessionIndex (l : PrimeGeFive) := ThetaPilotCarrier l

/-- Finite signed label index. -/
abbrev SignedLabelIndex (l : PrimeGeFive) := SignedLabel l.value

/-- Native selected-place index `V(S)`. -/
abbrev PlaceIndex {l : PrimeGeFive} (X : N8NativeInput l) := NativePlaces X.S

/-- Tensor tuple index family: a finite index `iota`, a place type `W i`,
actual native places over it, and the selected tuple.  This mirrors the C3
`tensorIndex/tensorPlaceIndex/tensorTuple` shape without using an arbitrary
external V. -/
structure TupleIndex {l : PrimeGeFive} (X : N8NativeInput l) where
  /-- Finite tensor-factor index. -/
  iota : Type u
  /-- Fintype for the tensor factors. -/
  fintype : Fintype iota
  /-- Place type at each tensor factor. -/
  W : iota → Type v
  /-- Actual native places. -/
  places : (i : iota) → W i → PlaceIndex X
  /-- The selected tuple. -/
  tuple : (i : iota) → W i

attribute [instance] TupleIndex.fintype

/-- A complete source-allowed choice index `alpha`: one theater column/row,
one finite procession component, one signed label, and one native place.
`columnRow` and `procession` are deliberately separate fields of different
types. -/
structure AlphaIndex {l : PrimeGeFive} (X : N8NativeInput l)
    (T : TupleIndex X) where
  /-- Integer theater column/row `(n,m)`. -/
  columnRow : IntegerColumnRow
  /-- Finite theta-pilot procession component; NOT an integer row. -/
  procession : ProcessionIndex l
  /-- Finite signed label. -/
  label : SignedLabelIndex l
  /-- Native selected place. -/
  place : PlaceIndex X

/-- Component index of `R_alpha`: a local place, a tensor factor/value, and a
procession/label component, all depending on the complete choice `a`. -/
structure RAlphaIndex {l : PrimeGeFive} {X : N8NativeInput l}
    {T : TupleIndex X} (a : AlphaIndex X T) where
  /-- Local component place. -/
  localPlace : PlaceIndex X
  /-- Tensor factor. -/
  tupleFactor : T.iota
  /-- Selected tuple value at the tensor factor. -/
  tupleValue : T.W tupleFactor
  /-- Finite procession component. -/
  procession : ProcessionIndex l
  /-- Finite signed label component. -/
  label : SignedLabelIndex l

/-- Region family `R_alpha` over an explicit output carrier `C`.  `C` is a
parameter because no source output-carrier type is frozen yet; no region is
asserted to exist. -/
structure RAlphaFamily {l : PrimeGeFive} (X : N8NativeInput l)
    (T : TupleIndex X) (C : Type w) where
  /-- The region `R_alpha` at a component index. -/
  R : (a : AlphaIndex X T) → RAlphaIndex a → Set C

/-- Union of the `R_alpha` components for one complete choice `a`. -/
def RAlphaFamily.componentUnion {l : PrimeGeFive} {X : N8NativeInput l}
    {T : TupleIndex X} {C : Type w} (D : RAlphaFamily X T C)
    (a : AlphaIndex X T) : Set C :=
  ⋃ r : RAlphaIndex a, D.R a r

/-- Union over all complete choices and components: `U = union_alpha R_alpha`. -/
def RAlphaFamily.U {l : PrimeGeFive} {X : N8NativeInput l}
    {T : TupleIndex X} {C : Type w} (D : RAlphaFamily X T C) : Set C :=
  ⋃ a : AlphaIndex X T, D.componentUnion a

/-- `R_alpha` is contained in the component union. -/
theorem RAlphaFamily.R_subset_componentUnion {l : PrimeGeFive}
    {X : N8NativeInput l} {T : TupleIndex X} {C : Type w}
    (D : RAlphaFamily X T C) (a : AlphaIndex X T) (r : RAlphaIndex a) :
    D.R a r ⊆ D.componentUnion a := by
  intro x hx
  exact Set.mem_iUnion.mpr ⟨r, hx⟩

/-- `R_alpha` is contained in `U`. -/
theorem RAlphaFamily.R_subset_U {l : PrimeGeFive} {X : N8NativeInput l}
    {T : TupleIndex X} {C : Type w} (D : RAlphaFamily X T C)
    (a : AlphaIndex X T) (r : RAlphaIndex a) :
    D.R a r ⊆ D.U := by
  intro x hx
  exact Set.mem_iUnion.mpr ⟨a, D.R_subset_componentUnion a r hx⟩

end LeanFormal.IUT.N8Closure.P6Indices