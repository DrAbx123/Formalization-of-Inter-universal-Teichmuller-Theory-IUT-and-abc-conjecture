import tmp.sheaf.xif.paper.S1215SourceSHEHDDCompatibilityActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.LocalFieldIntegralHullSpan
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullDeterminantLogVolumeReduction
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorLogShellRealization

/-!
# S1300: the actual HDD/hull+det rank/lattice, or the exact first field

The S1215 target asks for

  rank : Nat
  lattice : Theorem311Output I -> place -> Set (Fin rank -> localField v).

The tree contains an actual hull+det layer
(`HullDeterminantLogVolumeReduction`) and an actual local-field hull/lattice
layer (`LocalFieldProductHull`).  Neither supplies the HDD local lattice in
the S1215 shape:

* the hull+det layer is a `Prop`-valued finite-packet determinant
  specification (`HullDeterminantLogVolumeFrozenSpec`) plus the scalar
  `Cor312ComparisonData` card;
* the actual local-field hull layer works over an arbitrary finite family
  `E : J -> Type`, with an integral `O`-submodule `integralRing` and a hull
  `Set ((j : J) -> E j)`; it has no rank indexed by `Fin` and no
  identification of the factors with the S1215 local fields
  `(oneColumnStructure).localField v`;
* the actual arithmetic line bundle layer is rank-one and its localizations
  are rank-one `O_v`-submodules, not HDD rank/lattice data.

No `SourceHDDReadout` structure and no `HDD` declaration exist in
`LeanFormal`.  The separate `vendor/promachina` snapshot has an
`HDDCompositeData` (`descent` + `hullDetBridge`), but it is an upstream
region-comparison record outside the `LeanFormal` import path and has no
`rank` or local lattice either.  This file therefore does not manufacture a
lattice.  It records the exact first field, the conditional construction that a genuine
HDD tensor-hull source would give, and the actual donor shapes.  It does not
use the rank-one unit-section surrogates, a one-point index, or an arbitrary
set as a lattice.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.LocalFieldProductHull
open LeanFormal.IUT.LocalFieldPadicTensor

universe u v

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]

/-! ## 1. The exact first field -/

/-- The exact first field of `S1215HDDLocalLattice`, exposed as its two
components.  No inhabitant is supplied. -/
structure S1300HDDFirstField (I : Input Label Choice) where
  /-- The HDD local-lattice rank. -/
  rank : Nat
  /-- The HDD local lattice at each output and place, in the 1-column local
  field. -/
  lattice : Theorem311Output I →
    (v : NumberField.FinitePlace ℚ) →
      Set (Fin rank → (oneColumnStructure).localField v)

namespace S1300HDDFirstField

variable {I : Input Label Choice}

/-- The pair of first-field components is exactly an S1215 HDD local lattice. -/
def toLocalLattice (F : S1300HDDFirstField I) :
    S1215HDDLocalLattice (I := I) where
  rank := F.rank
  lattice := F.lattice

/-- Read the exact first field off an S1215 HDD local lattice. -/
def ofLocalLattice (L : S1215HDDLocalLattice (I := I)) :
    S1300HDDFirstField I where
  rank := L.rank
  lattice := L.lattice

@[simp] theorem toLocalLattice_rank (F : S1300HDDFirstField I) :
    (F.toLocalLattice (I := I)).rank = F.rank := rfl

@[simp] theorem toLocalLattice_lattice (F : S1300HDDFirstField I)
    (o : Theorem311Output I) (v : NumberField.FinitePlace ℚ) :
    (F.toLocalLattice (I := I)).lattice o v = F.lattice o v := rfl

@[simp] theorem ofLocalLattice_rank (L : S1215HDDLocalLattice (I := I)) :
    (ofLocalLattice (I := I) L).rank = L.rank := rfl

@[simp] theorem ofLocalLattice_lattice (L : S1215HDDLocalLattice (I := I))
    (o : Theorem311Output I) (v : NumberField.FinitePlace ℚ) :
    (ofLocalLattice (I := I) L).lattice o v = L.lattice o v := rfl

theorem toLocalLattice_ofLocalLattice (L : S1215HDDLocalLattice (I := I)) :
    (ofLocalLattice (I := I) L).toLocalLattice (I := I) = L := by
  cases L
  rfl

theorem ofLocalLattice_toLocalLattice (F : S1300HDDFirstField I) :
    ofLocalLattice (I := I) (F.toLocalLattice (I := I)) = F := by
  cases F
  rfl

/-- No hidden field: the first-field record is equivalent to the S1215
HDD local lattice. -/
def equivLocalLattice : S1300HDDFirstField I ≃ S1215HDDLocalLattice (I := I) where
  toFun := toLocalLattice (I := I)
  invFun := ofLocalLattice (I := I)
  left_inv := ofLocalLattice_toLocalLattice (I := I)
  right_inv := toLocalLattice_ofLocalLattice (I := I)

end S1300HDDFirstField

/-- Exact type recorded when no actual HDD source is available. -/
abbrev S1300HDDLocalLatticeRequired (I : Input Label Choice) : Type (v + 1) :=
  S1215HDDLocalLattice (I := I)

/-- Exact first field type: the S1215 HDD local lattice itself. -/
abbrev S1300HDDFirstFieldRequired (I : Input Label Choice) : Type (v + 1) :=
  S1300HDDFirstField I

/-! ## 2. What a genuine HDD tensor-hull source would have to supply -/

/-- A candidate HDD tensor-hull source in the shape of the actual local-field
hull+det donors: a finite local-field tensor family, its actual allowed-image
family, the hull data, the determinant bookkeeping, and the missing uniform
identification of every factor with the S1215 1-column local field.

The `image` field is the source's allowed-image family, not a chosen lattice;
the lattice below is actually `LocalFieldProductHull.hull` of that image,
transported by `localEquiv`.  No inhabitant of this structure is asserted. -/
structure S1300HDDHullDetSource (I : Input Label Choice) where
  /-- The rank: the number of local-field factors of the HDD tensor packet. -/
  rank : Nat
  /-- The actual finite family of local fields of the HDD tensor packet. -/
  E : Fin rank → Type
  /-- The normed-field structure on each factor. -/
  normedField : ∀ i, NormedField (E i)
  /-- The actual HDD allowed-image family, output-dependent. -/
  image : Theorem311Output I → Set ((i : Fin rank) → E i)
  /-- The actual compactness input of the hull construction. -/
  compact_closure : ∀ o, IsCompact (closure (image o))
  /-- The actual nonemptiness input of the hull construction. -/
  nonempty : ∀ o, (image o).Nonempty
  /-- The actual coordinatewise nondegeneracy input of the hull construction. -/
  coordinate_nonzero : ∀ (o) (i : Fin rank), ∃ x ∈ image o, x i ≠ 0
  /-- The missing uniform identification of every tensor factor with the
  1-column local field at every place. -/
  localEquiv : ∀ v : NumberField.FinitePlace ℚ,
    (i : Fin rank) → E i ≃+* (oneColumnStructure).localField v
  /-- The determinant bookkeeping of the actual hull+det layer. -/
  detData : DetTensorPowerLogVolumeBookkeeping (Set ((i : Fin rank) → E i))

namespace S1300HDDHullDetSource

variable {I : Input Label Choice}

/-- The actual local-field hull, transported to the 1-column local fields by
the source's uniform field identification. -/
noncomputable def lattice (D : S1300HDDHullDetSource I)
    (o : Theorem311Output I) (v : NumberField.FinitePlace ℚ) :
    Set (Fin D.rank → (oneColumnStructure).localField v) :=
  (fun x : (i : Fin D.rank) → D.E i =>
      fun i => D.localEquiv v i (x i)) ''
    @LocalFieldProductHull.hull (Fin D.rank) D.E D.normedField (D.image o)

/-- Conditional construction: a genuine HDD tensor-hull source produces the
S1215 HDD local lattice.  The source itself is not constructed here. -/
noncomputable def toS1215 (D : S1300HDDHullDetSource I) :
    S1215HDDLocalLattice (I := I) where
  rank := D.rank
  lattice := fun o v => D.lattice o v

@[simp] theorem toS1215_rank (D : S1300HDDHullDetSource I) :
    (D.toS1215 (I := I)).rank = D.rank := rfl

@[simp] theorem toS1215_lattice (D : S1300HDDHullDetSource I)
    (o : Theorem311Output I) (v : NumberField.FinitePlace ℚ) :
    (D.toS1215 (I := I)).lattice o v = D.lattice o v := rfl

/-- The constructed lattice is exactly the actual hull of the source image,
transported by the uniform local-field identification. -/
theorem toS1215_lattice_eq_hull (D : S1300HDDHullDetSource I)
    (o : Theorem311Output I) (v : NumberField.FinitePlace ℚ) :
    (D.toS1215 (I := I)).lattice o v =
      (fun x : (i : Fin D.rank) → D.E i =>
        fun i => D.localEquiv v i (x i)) ''
      @LocalFieldProductHull.hull (Fin D.rank) D.E D.normedField (D.image o) := rfl

end S1300HDDHullDetSource

/-! ## 3. Actual hull+det donor facts -/

/-- The actual hull+det frozen specification is `Prop`-valued; its realization
is a proof of finite-packet determinant identities.  It supplies no rank and
no local lattice. -/
abbrev S1300ActualHullDetSpec : Prop :=
  HullDeterminantLogVolumeFrozenSpec.{0, 0, 0, 0, 0, 0, 0, 0, 0}

theorem s1300ActualHullDetSpec_holds : S1300ActualHullDetSpec :=
  hullDeterminantLogVolumeFrozenSpec_holds

/-- The actual local-field integral span of a compact nondegenerate image is
the actual hull.  This is the real lattice theorem of the hull+det source; its
ambient family `E` is arbitrary and is not identified with the S1215 local
fields. -/
theorem s1300ActualIntegralSpan_eq_hull
    {J : Type*} [Finite J] {E : J → Type*} [∀ j, NormedField (E j)]
    (hna : ∀ j, IsNonarchimedean (Norm.norm : E j → ℝ))
    {S : Set ((j : J) → E j)} (hS : IsCompact S) (hne : S.Nonempty)
    (hcoord : ∀ j, ∃ x ∈ S, x j ≠ 0) :
    (Submodule.span (LocalFieldProductHull.integralRing hna) S :
      Set ((j : J) → E j)) = LocalFieldProductHull.hull S :=
  LocalFieldProductHull.integralSpan_eq_hull hna hS hne hcoord

/-! ## 4. Donor checks -/

section ActualDonorChecks

#check LocalFieldProductHull.hull
#check LocalFieldProductHull.regionModule
#check LocalFieldProductHull.integralSpan_eq_hull
#check LocalFieldPadicTensor.exists_realized_tensorLogShell_hull
#check HullDeterminantLogVolumeFrozenSpec
#check hullDeterminantLogVolumeFrozenSpec_holds
#check DetTensorPowerLogVolumeBookkeeping
#check Cor312ComparisonData
#check S1300HDDLocalLatticeRequired
#check S1300HDDFirstFieldRequired
#check S1300HDDHullDetSource

end ActualDonorChecks

end LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual

end
