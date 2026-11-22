import tmp.sheaf.xif.paper.S1727SectionsFPrimeActual
import tmp.sheaf.xif.paper.S1881D9D7bActual

/-!
# S1888: the actual D7b local-group carrier family over the S1732 line

S1881 proved that the S1732 D7 input is definitionally
`S1727SectionFirstMissing`, whose first field is

  `localGroupCarrier : (S1727Layer l).valuationCarrier -> Type`.

This file attacks that first field.  It does *not* fill it with `PUnit`, a
trivial group, an arbitrary type, or the arithmetic local Galois group
`G_v = Gal(K_v^sep / K_v)`.  Instead it does two things.

## 1. The exact curve-side local group at one place

For a selected place `x` of `K = F' = S1720Field`, the paper's local group
`Pi_Xv` is the etale fundamental group of the base-changed hyperbolic
orbicurve `X_v` of type `(1,l-tors)`.  The structure `S1888LocalGroupAt l x`
records exactly that datum over the *actual* local field of `x`:

* `S1888LocalFieldAt x.1` is the adic completion at a finite place and the
  real/complex completion at an archimedean place;
* `X : HyperbolicOrbicurve (S1888LocalFieldAt x.1)` is a local hyperbolic
  orbicurve with `X.signature = sourceTypeOneLTorsion l`;
* `groups : OrbicurveFundamentalGroupData X (AbsoluteGaloisProfinite ...)`
  certifies the curve-side etale fundamental group of `X`, together with its
  actual surjection onto the arithmetic local Galois group.

The carrier of the local group is `groups.arithmeticGroup`; the arithmetic
group `G_v` is only the codomain of the projection.  Thus the carrier is a
factor of the curve group, not a relabelled `G_v`: the certification
`groups.arithmetic` is an actual `OrbicurveEtaleFundamentalGroup` of `X`.

## 2. The family and the exact first missing

`S1888D7bLocalGroupFamily l` is a place-indexed family of the above local
group data.  Its carrier family

  `S1888D7bLocalGroupFamily.carrier : (S1727Layer l).valuationCarrier -> Type`

is the precise first field.  This family is *not* constructed: no actual
orbifold etale fundamental group of a curve exists in the tree (the D6 line
records the same absence in `S1726FirstMissing`).  The family is exposed as a
type; `S1888D7bFirstMissing l` is its nonemptiness.  This is the exact first
missing object, one level below `S1727SectionFirstMissing`.

What *is* constructed from the family is the whole D7b supply
`S1727SectionFirstMissing l`:

* the modified carrier is the pullback of the carrier family along the
  canonical place-lift `sectionRightInverse`;
* the pointwise local-group section is the canonical transport
  `Equiv.cast` along `section_left_inverse`; it is bijective by construction;
* the finite/infinite place data are the actual kind-preservation statements
  of the selected place section (proved from `comap_place_isFinite_iff` /
  `comap_place_isInfinite_iff`).

Hence

  `S1888D7bLocalGroupFamily l -> Nonempty (S1727SectionFirstMissing l)`,

and the first field of the constructed supply is definitionally the carrier
family.  The converse implication is deliberately not asserted: an abstract
D7b supply need not be realized by actual local orbicurves.

## 3. The global D9/D7b orbicurves are not the actual S1726 D6 object

`S1888D7bGlobalGeometry` records the global objects from which the paper's
local groups are obtained by base change: `X_K` of type `(1,l-tors)`, `C_K`
of type `(1,l-tors)^pm`, the finite etale cover, and the certified
fundamental group of `X_K`.  The actual S1726 orbicurve is the once-punctured
elliptic curve of type `(1,1)`, not `X_K` or `C_K`; its signature is
different, so it cannot be used as a substitute for the missing local-group
source.  This is proved below (`xK_ne_S1726Orbicurve`,
`cK_ne_S1726Orbicurve`).

No `sorry`, `admit`, `True`/`PUnit` substitution, arbitrary group, or new
axiom is used.  The only axioms are the standard `propext`,
`Classical.choice`, and `Quot.sound`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S1888D7bLocalGroupActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1727SectionsFPrimeActual
open LeanFormal.IUT.XiFPaper.S1881D9D7bActual

/-! ## 1. The actual local field at a place of `F'` -/

/-- The actual local field at a place of a number field: the adic completion
at a finite place, and the real or complex completion at an archimedean
place.  This is the field `K_v` over which the paper's local orbicurve `X_v`
lives. -/
noncomputable def S1888LocalFieldAt {K : Type} [Field K] [NumberField K]
    (x : NumberFieldPlace K) : Type :=
  match x with
  | NumberFieldPlace.finite p => p.maximalIdeal.adicCompletion K
  | NumberFieldPlace.infinite p => by
      classical
      exact if h : p.IsReal then ℝ else ℂ

noncomputable instance S1888LocalFieldAt.instField {K : Type} [Field K]
    [NumberField K] (x : NumberFieldPlace K) :
    Field (S1888LocalFieldAt x) := by
  cases x with
  | finite p =>
      exact inferInstanceAs (Field (p.maximalIdeal.adicCompletion K))
  | infinite p =>
      classical
      dsimp [S1888LocalFieldAt]
      split <;> infer_instance

/-- At a finite place the local field is the actual adic completion. -/
@[simp] theorem S1888LocalFieldAt_finite {K : Type} [Field K] [NumberField K]
    (p : NumberField.FinitePlace K) :
    S1888LocalFieldAt (NumberFieldPlace.finite p) =
      p.maximalIdeal.adicCompletion K := rfl

/-- At a real archimedean place the local field is `R`. -/
theorem S1888LocalFieldAt_infinite_real {K : Type} [Field K] [NumberField K]
    (p : NumberField.InfinitePlace K) (h : p.IsReal) :
    S1888LocalFieldAt (NumberFieldPlace.infinite p) = ℝ := by
  classical
  dsimp [S1888LocalFieldAt]
  exact dif_pos h

/-- At a complex archimedean place the local field is `C`. -/
theorem S1888LocalFieldAt_infinite_complex {K : Type} [Field K] [NumberField K]
    (p : NumberField.InfinitePlace K) (h : ¬ p.IsReal) :
    S1888LocalFieldAt (NumberFieldPlace.infinite p) = ℂ := by
  classical
  dsimp [S1888LocalFieldAt]
  exact dif_neg h

/-! ## 2. The curve-side local group at one selected place -/

variable (l : PrimeGeFive)

/-- The paper's local group datum at one selected place `x`: an actual
hyperbolic orbicurve `X_v` of type `(1,l-tors)` over the actual local field
`K_v`, together with its certified etale fundamental group over the actual
absolute Galois group of `K_v`.

The carrier of the local group is `groups.arithmeticGroup`, not the
arithmetic group `AbsoluteGaloisProfinite (S1888LocalFieldAt x.1)`; the
latter is only the codomain of `groups.projection`.

This is the local part of the paper's datum: the relation to a single global
`X_K` (base change to `K_v`) is part of the separate
`S1888D7bGlobalGeometry` and is not encoded in this local structure.  The
clause's first field is exactly the place-indexed family of these local
groups. -/
structure S1888LocalGroupAt (x : (S1727Layer l).valuationCarrier) where
  /-- The local hyperbolic orbicurve `X_v`, of paper type `(1,l-tors)`. -/
  X : Iut.HyperbolicOrbicurve (S1888LocalFieldAt x.1)
  /-- `X_v` has the paper's local type. -/
  X_signature : X.signature = sourceTypeOneLTorsion l
  /-- The certified etale fundamental group of `X_v`, with its actual
  projection onto the absolute Galois group of the local field. -/
  groups : Iut.OrbicurveFundamentalGroupData X
    (Iut.AbsoluteGaloisProfinite (S1888LocalFieldAt x.1))

namespace S1888LocalGroupAt

variable {l : PrimeGeFive} {x : (S1727Layer l).valuationCarrier}

/-- The carrier of the local group `Pi_Xv`: the underlying type of the
certified etale fundamental group of the local orbicurve. -/
noncomputable def carrier (D : S1888LocalGroupAt l x) : Type :=
  ↥D.groups.arithmeticGroup

@[simp] theorem carrier_eq (D : S1888LocalGroupAt l x) :
    D.carrier = ↥D.groups.arithmeticGroup := rfl

/-- The carrier is certified as the curve-side etale fundamental group of the
actual local orbicurve; it is not an arbitrary type. -/
noncomputable def carrier_certified (D : S1888LocalGroupAt l x) :
    Iut.OrbicurveEtaleFundamentalGroup D.X D.groups.arithmeticGroup :=
  D.groups.arithmetic

/-- The carrier surjects onto the actual arithmetic local Galois group
`G_v = Gal(K_v^sep / K_v)`.  The paper's group `Pi_Xv` is the curve-side
group above `G_v`, not `G_v` itself. -/
theorem carrier_surjects_arithmetic_localGroup
    (D : S1888LocalGroupAt l x) :
    ∃ f : D.carrier → Iut.AbsoluteGaloisProfinite (S1888LocalFieldAt x.1),
      Function.Surjective f :=
  ⟨D.groups.projection, D.groups.projection_surjective⟩

/-- The exact sequence of the local group: the geometric group is the closed
kernel of the actual projection. -/
noncomputable def localExactSequence (D : S1888LocalGroupAt l x) :
    Iut.ProfiniteFundamentalExactSequence
      D.groups.geometric.group D.groups.arithmeticGroup
      (Iut.AbsoluteGaloisProfinite (S1888LocalFieldAt x.1)) :=
  D.groups.exactSequence

end S1888LocalGroupAt

/-! ## 3. The place-indexed family and its first field -/

/-- The exact D7b local-group family: at every selected place of `F'`, the
curve-side local group datum of Section 2.  This is the precise first missing
datum; it is exposed as a type, not inhabited. -/
structure S1888D7bLocalGroupFamily (l : PrimeGeFive) where
  /-- The local group datum at each selected place. -/
  localGroup : (x : (S1727Layer l).valuationCarrier) →
    S1888LocalGroupAt l x

namespace S1888D7bLocalGroupFamily

variable {l : PrimeGeFive}

/-- The carrier family `x |-> Pi_Xv`. -/
noncomputable def carrier (D : S1888D7bLocalGroupFamily l) :
    (S1727Layer l).valuationCarrier → Type :=
  fun x => S1888LocalGroupAt.carrier (D.localGroup x)

@[simp] theorem carrier_apply (D : S1888D7bLocalGroupFamily l)
    (x : (S1727Layer l).valuationCarrier) :
    D.carrier x = ↥(D.localGroup x).groups.arithmeticGroup := rfl

/-- The first field of D7b realized by the family. -/
noncomputable def toFirstField (D : S1888D7bLocalGroupFamily l) :
    S1727D7FirstField l :=
  D.carrier

@[simp] theorem toFirstField_apply (D : S1888D7bLocalGroupFamily l)
    (x : (S1727Layer l).valuationCarrier) :
    D.toFirstField x = ↥(D.localGroup x).groups.arithmeticGroup := rfl

/-- The modified carrier is the pullback of the local-group family along the
canonical place-lift `V_mod -> V`; it is canonically determined by the first
field and the place section. -/
noncomputable def modifiedCarrier (D : S1888D7bLocalGroupFamily l) :
    (S1727Layer l).modifiedValuationCarrier → Type :=
  fun y => D.carrier ((S1727Layer l).sectionRightInverse y)

/-- The pointwise local-group section is the canonical transport of the
carrier along the left inverse of the place section.  It is bijective by
construction and does not add a second independent local-group datum. -/
noncomputable def sectionEquiv (D : S1888D7bLocalGroupFamily l)
    (x : (S1727Layer l).valuationCarrier) :
    D.carrier x ≃ D.modifiedCarrier ((S1727Layer l).sectionMap x) :=
  Equiv.cast (congrArg D.carrier
    ((S1727Layer l).section_left_inverse x).symm)

@[simp] theorem sectionEquiv_apply (D : S1888D7bLocalGroupFamily l)
    (x : (S1727Layer l).valuationCarrier) (g : D.carrier x) :
    D.sectionEquiv x g =
      cast (congrArg D.carrier
        ((S1727Layer l).section_left_inverse x).symm) g := rfl

/-! ### Actual finite/infinite place data -/

/-- The finite-place data of Definition 3.1(e): the restriction of a selected
finite place is finite.  This is the actual kind-preservation statement of
the place-section layer. -/
def finitePlaceData (D : S1888D7bLocalGroupFamily l) : Prop :=
  ∀ x : (S1727Layer l).valuationCarrier,
    NumberFieldPlace.IsFinite x.1 →
      NumberFieldPlace.IsFinite ((S1727Layer l).sectionMap x)

theorem finitePlaceData_proved (D : S1888D7bLocalGroupFamily l) :
    D.finitePlaceData := by
  intro x hx
  rw [S1727Layer_sectionMap_apply l x]
  exact (comap_place_isFinite_iff (k := (S1727A l).Fmod) x.1).mpr hx

/-- The infinite-place data of Definition 3.1(e): the restriction of a
selected archimedean place is archimedean. -/
def infinitePlaceData (D : S1888D7bLocalGroupFamily l) : Prop :=
  ∀ x : (S1727Layer l).valuationCarrier,
    NumberFieldPlace.IsInfinite x.1 →
      NumberFieldPlace.IsInfinite ((S1727Layer l).sectionMap x)

theorem infinitePlaceData_proved (D : S1888D7bLocalGroupFamily l) :
    D.infinitePlaceData := by
  intro x hx
  rw [S1727Layer_sectionMap_apply l x]
  exact (comap_place_isInfinite_iff (k := (S1727A l).Fmod) x.1).mpr hx

/-! ### The full D7b supply constructed from the family -/

/-- **Construction.**  A place-indexed family of actual curve-side local
groups produces a full D7b supply over the canonical place-section layer.
The modified carrier and the pointwise bijection are canonical; the
finite/infinite place data are the actual kind-preservation facts. -/
noncomputable def toSupply (D : S1888D7bLocalGroupFamily l) :
    S1727SectionFirstMissing l where
  localGroupCarrier := D.carrier
  modifiedLocalGroupCarrier := D.modifiedCarrier
  localGroupSection := fun x => D.sectionEquiv x
  localGroupSection_injective := fun x => (D.sectionEquiv x).injective
  localGroupSection_surjective := fun x => (D.sectionEquiv x).surjective
  finitePlaceData := D.finitePlaceData
  finitePlaceData_proved := D.finitePlaceData_proved
  infinitePlaceData := D.infinitePlaceData
  infinitePlaceData_proved := D.infinitePlaceData_proved

@[simp] theorem toSupply_localGroupCarrier
    (D : S1888D7bLocalGroupFamily l) :
    D.toSupply.localGroupCarrier = D.carrier := rfl

@[simp] theorem toSupply_modifiedLocalGroupCarrier
    (D : S1888D7bLocalGroupFamily l) :
    D.toSupply.modifiedLocalGroupCarrier = D.modifiedCarrier := rfl

@[simp] theorem toSupply_finitePlaceData
    (D : S1888D7bLocalGroupFamily l) :
    D.toSupply.finitePlaceData = D.finitePlaceData := rfl

@[simp] theorem toSupply_infinitePlaceData
    (D : S1888D7bLocalGroupFamily l) :
    D.toSupply.infinitePlaceData = D.infinitePlaceData := rfl

/-- The first field of the constructed supply is definitionally the carrier
family of the actual local groups. -/
theorem toSupply_firstField (D : S1888D7bLocalGroupFamily l) :
    D.toSupply.localGroupCarrier = D.toFirstField := rfl

end S1888D7bLocalGroupFamily

/-! ## 4. Connection with `S1727SectionFirstMissing` -/

/-- The constructed full D7b supply exists whenever the actual local-group
family exists. -/
theorem S1888D7b_supply_nonempty_of_family {l : PrimeGeFive}
    (D : S1888D7bLocalGroupFamily l) :
    Nonempty (S1727SectionFirstMissing l) :=
  ⟨D.toSupply⟩

/-- The exact first-field/tail decomposition of S1727 is inherited: a family
supplies the first field and the tail, hence the S1727 nonemptiness form. -/
theorem S1888D7b_firstField_tail_of_family {l : PrimeGeFive}
    (D : S1888D7bLocalGroupFamily l) :
    ∃ G0 : S1727D7FirstField l, Nonempty (S1727D7Tail l G0) :=
  (S1727SectionFirstMissing_nonempty_iff_firstField_tail l).mp
    (S1888D7b_supply_nonempty_of_family D)

/-- **The exact first missing object**: a place-indexed family of actual
curve-side local groups `Pi_Xv` over the selected places of `F'`. -/
def S1888D7bFirstMissing (l : PrimeGeFive) : Prop :=
  Nonempty (S1888D7bLocalGroupFamily l)

/-- The missing family is sufficient for the full D7b supply. -/
theorem S1888D7bFirstMissing.supply {l : PrimeGeFive}
    (h : S1888D7bFirstMissing l) :
    Nonempty (S1727SectionFirstMissing l) := by
  rcases h with ⟨D⟩
  exact S1888D7b_supply_nonempty_of_family D

/-- The same nonemptiness transported across the definitional identification
`S1732D7Input l = S1727SectionFirstMissing l` recorded in S1881. -/
theorem S1888D7bFirstMissing.supply_S1732 {l : PrimeGeFive}
    (h : S1888D7bFirstMissing l) :
    Nonempty
      (LeanFormal.IUT.XiFPaper.S1732SourceAssemblyActual.S1732D7Input l) :=
  h.supply

/-- The missing family is sufficient for the S1727 first-field/tail
decomposition. -/
theorem S1888D7bFirstMissing.firstField_tail {l : PrimeGeFive}
    (h : S1888D7bFirstMissing l) :
    ∃ G0 : S1727D7FirstField l, Nonempty (S1727D7Tail l G0) := by
  rcases h with ⟨D⟩
  exact S1888D7b_firstField_tail_of_family D

/-- A first field of a D7b supply that is realized by the actual local-group
family. -/
def S1888D7bRealizedFirstField (l : PrimeGeFive) : Type 1 :=
  {G0 : S1727D7FirstField l //
    ∃ D : S1888D7bLocalGroupFamily l, D.toFirstField = G0}

/-- Every actual local-group family realizes its first field. -/
noncomputable def S1888D7bRealizedFirstField.ofFamily
    {l : PrimeGeFive} (D : S1888D7bLocalGroupFamily l) :
    S1888D7bRealizedFirstField l :=
  ⟨D.toFirstField, ⟨D, rfl⟩⟩

/-- The exact first missing object is precisely the existence of a first
field realized by actual curve-side local groups. -/
theorem S1888D7bFirstMissing_iff_realizedFirstField (l : PrimeGeFive) :
    S1888D7bFirstMissing l ↔
      Nonempty (S1888D7bRealizedFirstField l) := by
  constructor
  · rintro ⟨D⟩
    exact ⟨S1888D7bRealizedFirstField.ofFamily D⟩
  · rintro ⟨⟨G0, D, _h⟩⟩
    exact ⟨D⟩

/-- A realized first field extends to a full D7b supply whose first field is
literally that field. -/
theorem S1888D7bRealizedFirstField.supply {l : PrimeGeFive}
    (p : S1888D7bRealizedFirstField l) :
    ∃ G : S1727SectionFirstMissing l, G.localGroupCarrier = p.1 := by
  rcases p.2 with ⟨D, h⟩
  refine ⟨D.toSupply, ?_⟩
  rw [S1888D7bLocalGroupFamily.toSupply_localGroupCarrier]
  exact h

/-- **Exact connection with S1727.**  The missing family is exactly a
realization of the first field of some D7b supply: the family's carrier is
the first field, and the supply's first field is that carrier. -/
theorem S1888D7bFirstMissing_iff_exists_supply_firstField (l : PrimeGeFive) :
    S1888D7bFirstMissing l ↔
      ∃ (G : S1727SectionFirstMissing l)
        (D : S1888D7bLocalGroupFamily l),
        D.toFirstField = G.localGroupCarrier := by
  constructor
  · rintro ⟨D⟩
    exact ⟨D.toSupply, D, rfl⟩
  · rintro ⟨G, D, _h⟩
    exact ⟨D⟩

/-! ## 5. The global D9/D7b geometry is not the actual S1726 D6 object -/

/-- The global geometric objects from which the paper's local groups are
obtained by base change: `X_K` of type `(1,l-tors)`, `C_K` of type
`(1,l-tors)^pm`, the finite etale cover `X_K -> C_K`, and the certified
etale fundamental group of `X_K`.

This structure is *not* constructed; it records the exact global D9/D7b
geometry.  It is separated from the local-group family so that the family
is not confused with a global orbicurve datum. -/
structure S1888D7bGlobalGeometry (l : PrimeGeFive) where
  /-- The global `X_K` of paper type `(1,l-tors)`. -/
  xK : Iut.HyperbolicOrbicurve (S1727A l).K
  xK_signature : xK.signature = sourceTypeOneLTorsion l
  /-- The global `C_K` of paper type `(1,l-tors)^pm`. -/
  cK : Iut.HyperbolicOrbicurve (S1727A l).K
  cK_signature : cK.signature = sourceTypeOneLTorsionPlusMinus l
  /-- The natural finite etale cover `X_K -> C_K`. -/
  cover : xK.Hom cK
  cover_finiteEtale : Iut.EtaleStackFiniteEtaleMorphism cover
  /-- The certified etale fundamental group of `X_K`. -/
  xKGroups : Iut.OrbicurveFundamentalGroupData xK
    (Iut.AbsoluteGaloisProfinite (S1727A l).K)

namespace S1888D7bGlobalGeometry

variable {l : PrimeGeFive} (G : S1888D7bGlobalGeometry l)

/-- The global `X_K` of the D9/D7b geometry is not the actual S1726 D6
orbicurve: the signatures `(1,l-tors)` and `(1,1)` are different.  Hence the
S1726 D6 object cannot be used as a substitute for the missing global
local-group source. -/
theorem xK_ne_S1726Orbicurve : G.xK ≠ S1726Orbicurve := by
  intro h
  have hsig : G.xK.signature = S1726Orbicurve.signature := congrArg _ h
  exact S1881S1726_not_XK l (G.xK_signature.symm.trans hsig).symm

/-- The global `C_K` is not the actual S1726 D6 orbicurve either. -/
theorem cK_ne_S1726Orbicurve : G.cK ≠ S1726Orbicurve := by
  intro h
  have hsig : G.cK.signature = S1726Orbicurve.signature := congrArg _ h
  exact S1881S1726_not_CK l (G.cK_signature.symm.trans hsig).symm

/-- The global D7b orbicurve signature is not the S1726 signature. -/
theorem xK_signature_ne_S1726Orbicurve_signature :
    G.xK.signature ≠ S1726Orbicurve.signature := by
  intro h
  exact S1881S1726_not_XK l (G.xK_signature.symm.trans h).symm

end S1888D7bGlobalGeometry

/-! ## 6. Axiom footprint -/

#print axioms S1888LocalFieldAt
#print axioms S1888LocalFieldAt_infinite_real
#print axioms S1888LocalGroupAt.carrier_certified
#print axioms S1888LocalGroupAt.localExactSequence
#print axioms S1888D7bLocalGroupFamily.toSupply
#print axioms S1888D7bLocalGroupFamily.finitePlaceData_proved
#print axioms S1888D7bLocalGroupFamily.infinitePlaceData_proved
#print axioms S1888D7b_supply_nonempty_of_family
#print axioms S1888D7bFirstMissing.supply_S1732
#print axioms S1888D7b_firstField_tail_of_family
#print axioms S1888D7bFirstMissing_iff_realizedFirstField
#print axioms S1888D7bFirstMissing_iff_exists_supply_firstField
#print axioms S1888D7bRealizedFirstField.supply
#print axioms S1888D7bGlobalGeometry.xK_ne_S1726Orbicurve
#print axioms S1888D7bGlobalGeometry.cK_ne_S1726Orbicurve

end LeanFormal.IUT.XiFPaper.S1888D7bLocalGroupActual

end
