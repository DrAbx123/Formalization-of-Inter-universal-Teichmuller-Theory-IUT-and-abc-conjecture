import tmp.sheaf.xif.paper.S1280SourceDefinition31Actual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCommonPrimeCompletion
import LeanFormal.IUT.IUTII.Frobenioid.Example36GaussianLocalGalois
import LeanFormal.IUT.IUTII.Frobenioid.Example36OrbicurveFeasibility

/-!
# S1312: the actual D6/D7b place bridge at the concrete Gaussian place

Consumer: the D6/D7b line of IUT I, Definition 3.1(d)-(e).  S1280 supplies the
actual D3/D4 data (the Gaussian arithmetic input, the actual bad-place
selection, the finite bad index, and the reduction cards/clause); its D5
torsion slot remains the exact open card.  This file adds only what the actual
places and the actual Gaussian local field determine:

* the actual bad-place bridge
  `S1312BadPlaceAtPrime : Bad (S1280Selection l) -> FinitePlaceAtPrime Fmod 5`,
  with the proof that its value is literally the concrete Gaussian place
  above `5`, together with injectivity and the exact range description, and
  the general own-prime forms `S1312BadAtOwnPrime` /
  `S1312SelectedFiniteAtOwnPrime` for every bad place and every finite
  selected place;
* the selected place above the bad place,
  `S1312SelectedBadPlace : Selected (S1280Selection l)`, proved to be the
  finite place `concreteGaussianFivePlace` and to lie in the Definition
  3.1(e) bad fibre `V_bad`, and its fixed-prime-5 form
  `S1312SelectedBadPlaceAtPrime : FinitePlaceAtPrime K 5`;
* the actual local field at that place (the adic completion, rewritten as
  `Completion` of the bridged finite place), the actual base-changed local
  curve, the actual arithmetic local Galois group
  `G_v = AbsoluteGaloisProfinite (K_v)`, the certified arithmetic anabelioid
  `B(G_v)`, and the actual local unit group;
* the concrete package `S1312PlaceBridgeActual` bundling the place bridge
  and the actual local field/Galois/anabelioid data.

The exact boundary is stated, not crossed:

* D6: the first field of the exact missing D6 object
  (`MissingD6GeometricRealization F`) is the actual curve
  `(S1280Arithmetic l).curve`; the first D6 field not determined by the
  concrete data is the etale stack fiber `Iut.EtaleStackPseudofunctor F`.
  No orbicurve, stack, or fundamental group is manufactured.
* D7b: the first field of `D7LocalGroupSectionSupply` for the canonical
  place-section layer is the local-group carrier family
  `L.valuationCarrier -> Type`.  It is not constructed here.  The actual
  arithmetic local Galois group `G_v` is the *arithmetic* local group; it is
  not the curve-side local group Pi_Xv inside Pi_Cv of Definition 3.1(e).
  Hence this file does not assert an inhabitant of D7b, does not fill the
  D7b place-data slots, and does not touch torsion, orbicurves, cusps, or the
  D9 compatibility fields.

The file contains no `sorry`, no new axiom, and no PUnit/True/trivial-group
substitution.  Axiom footprints are printed at the end.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S1312D7LocalGroupActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.InitialThetaSource.Definition31D4D9Supply
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.GaussianPlaceStrip
open LeanFormal.IUT.IUTII.Frobenioid.Example36.GaussianLocalGalois
open LeanFormal.IUT.IUTII.Frobenioid.Example36.OrbicurveFeasibility

local instance s1312GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-! ## 1. The actual place bridge -/

/-- Restriction along the identity tower `Fmod = K = Q(i)` is the identity on
finite places of `K`.  This is the `K`-side companion of
`S1280_comap_eq_self`. -/
theorem S1312ComapKEqSelf (l : PrimeGeFive)
    (q : NumberField.FinitePlace (S1280Arithmetic l).K) :
    NumberFieldFinitePlace.comap (k := (S1280Arithmetic l).Fmod) q = q := by
  apply NumberField.FinitePlace.maximalIdeal_injective
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rw [NumberFieldFinitePlace.comap_maximalIdeal]
  exact Ideal.comap_id _

/-- The chosen finite lift along the identity tower is the place itself. -/
theorem S1312FiniteLiftKEqSelf (l : PrimeGeFive)
    (p : NumberField.FinitePlace (S1280Arithmetic l).Fmod) :
    @NumberFieldPlace.finiteLift (S1280Arithmetic l).Fmod (S1280Arithmetic l).K
      (S1280Arithmetic l).fieldFmod (S1280Arithmetic l).numberFieldFmod
      (S1280Arithmetic l).fieldK (S1280Arithmetic l).numberFieldK
      (S1280Arithmetic l).algebraFmodK p = p := by
  have h := NumberFieldPlace.comap_finiteLift
    (k := (S1280Arithmetic l).Fmod) (K := (S1280Arithmetic l).K)
    (place := p)
  have hcomp : NumberFieldFinitePlace.comap (k := (S1280Arithmetic l).Fmod)
      (NumberFieldPlace.finiteLift (K := (S1280Arithmetic l).K) p) =
      NumberFieldPlace.finiteLift (K := (S1280Arithmetic l).K) p :=
    S1312ComapKEqSelf l _
  rw [hcomp] at h
  exact h

/-- The actual rational prime under the concrete Gaussian place above `5` is
`5`.  This is the computation used by `FinitePlaceAtPrime`; it is not a new
hypothesis. -/
theorem S1312CompletionRationalPrimeConcreteGaussianFivePlace :
    completionRationalPrime (concreteGaussianFivePlace) = concreteFivePrime := by
  rw [completionRationalPrime, concreteGaussianFivePlace_comap,
    concreteFivePlace_maximalIdeal, concreteFiveHeightOne]
  exact Equiv.apply_symm_apply _ _

/-- Every bad place of the S1280 selection is the concrete Gaussian place. -/
theorem S1312BadEqConcrete (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) : b.1 = concreteGaussianFivePlace := by
  have h : b.1 ∈ ({concreteGaussianFivePlace} :
      Set (NumberField.FinitePlace (S1280Arithmetic l).Fmod)) := by
    simpa only [S1280Selection_V_mod_bad] using b.2
  exact Set.eq_of_mem_singleton h

/-- The actual bad-place bridge `Bad (S1280Selection l) -> FinitePlaceAtPrime
Fmod 5`.  The value is the concrete Gaussian place; the proof component is the
computed rational prime `5`. -/
noncomputable def S1312BadPlaceAtPrime (l : PrimeGeFive)
    (_b : Bad (S1280Selection l)) :
    FinitePlaceAtPrime (S1280Arithmetic l).Fmod 5 where
  val := concreteGaussianFivePlace
  property := congrArg Subtype.val
    S1312CompletionRationalPrimeConcreteGaussianFivePlace

@[simp] theorem S1312BadPlaceAtPrime_val (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) :
    (S1312BadPlaceAtPrime l b).val = concreteGaussianFivePlace := rfl

/-- The bridged place is the bad place itself (as an actual finite place). -/
theorem S1312BadPlaceAtPrime_spec (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) :
    b.1 = (S1312BadPlaceAtPrime l b).val := by
  rw [S1312BadPlaceAtPrime_val]
  exact S1312BadEqConcrete l b

/-- The general finite-place form of a bad place, at its own computed rational
prime.  This is the non-specialized instance behind the fixed-prime-5 bridge. -/
noncomputable def S1312BadAtOwnPrime (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) :
    FinitePlaceAtPrime (S1280Arithmetic l).Fmod
      (completionRationalPrime b.1).val :=
  ⟨b.1, rfl⟩

@[simp] theorem S1312BadAtOwnPrime_val (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) :
    (S1312BadAtOwnPrime l b).val = b.1 := rfl

/-- The fixed-prime-5 bridge has the same underlying place as the general
own-prime form. -/
theorem S1312BadPlaceAtPrime_eq_ownPrime (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) :
    (S1312BadPlaceAtPrime l b).val = (S1312BadAtOwnPrime l b).val := by
  rw [S1312BadPlaceAtPrime_val]
  exact (S1312BadEqConcrete l b).symm

theorem S1312BadPlaceAtPrime_injective (l : PrimeGeFive) :
    Function.Injective (S1312BadPlaceAtPrime l) := by
  intro a b _
  haveI := S1280Bad_subsingleton l
  exact Subsingleton.elim a b

/-- The range of the bad-place bridge is exactly the fibre over the concrete
Gaussian place inside `FinitePlaceAtPrime Fmod 5`. -/
theorem S1312BadPlaceAtPrime_range (l : PrimeGeFive) :
    Set.range (S1312BadPlaceAtPrime l) =
      {p : FinitePlaceAtPrime (S1280Arithmetic l).Fmod 5 |
        p.val = concreteGaussianFivePlace} := by
  ext p
  constructor
  · rintro ⟨b, rfl⟩
    exact S1312BadPlaceAtPrime_val l b
  · intro hp
    have hne : Nonempty (Bad (S1280Selection l)) := by
      rcases (S1280Selection l).V_mod_bad_nonempty with ⟨q, hq⟩
      exact ⟨⟨q, hq⟩⟩
    refine ⟨Classical.choice hne, ?_⟩
    apply Subtype.ext
    rw [S1312BadPlaceAtPrime_val]
    exact hp.symm

/-- The canonical selected place above the actual bad place: the point of
`Selected (S1280Selection l)` corresponding to `concreteGaussianFivePlace`. -/
noncomputable def S1312SelectedBadPlace (l : PrimeGeFive) :
    Selected (S1280Selection l) :=
  finiteToV (S1280Selection l) concreteGaussianFivePlace

/-- The selected place above the bad place is the finite place given by the
concrete Gaussian place. -/
theorem S1312SelectedBadPlace_val (l : PrimeGeFive) :
    (S1312SelectedBadPlace l).1 = NumberFieldPlace.finite
      (concreteGaussianFivePlace) := by
  unfold S1312SelectedBadPlace finiteToV
  rw [SourcePlaceSelection.V_mod_bijection_apply]
  change NumberFieldPlace.finite
      (@NumberFieldPlace.finiteLift (S1280Arithmetic l).Fmod (S1280Arithmetic l).K
        (S1280Arithmetic l).fieldFmod (S1280Arithmetic l).numberFieldFmod
        (S1280Arithmetic l).fieldK (S1280Arithmetic l).numberFieldK
        (S1280Arithmetic l).algebraFmodK (concreteGaussianFivePlace)) =
    NumberFieldPlace.finite (concreteGaussianFivePlace)
  rw [S1312FiniteLiftKEqSelf]
  rfl

/-- The selected place above the bad place lies in the bad fibre `V_bad` of
Definition 3.1(e). -/
theorem S1312SelectedBadPlace_mem_bad (l : PrimeGeFive) :
    S1312SelectedBadPlace l ∈ (S1280Selection l).V_bad := by
  unfold S1312SelectedBadPlace finiteToV
  exact SourcePlaceSelection.selected_bad_place_mem (S1280Selection l)
    concreteGaussianFivePlace (by
      rw [S1280Selection_V_mod_bad]
      exact Set.mem_singleton _)

/-- The selected bad place as a `FinitePlaceAtPrime K 5`. -/
noncomputable def S1312SelectedBadPlaceAtPrime (l : PrimeGeFive) :
    FinitePlaceAtPrime (S1280Arithmetic l).K 5 where
  val := concreteGaussianFivePlace
  property := congrArg Subtype.val
    S1312CompletionRationalPrimeConcreteGaussianFivePlace

@[simp] theorem S1312SelectedBadPlaceAtPrime_val (l : PrimeGeFive) :
    (S1312SelectedBadPlaceAtPrime l).val = concreteGaussianFivePlace := rfl

/-- The selected bad place is the finite place underlying its fixed-prime-5
form. -/
theorem S1312SelectedBadPlaceAtPrime_eq_finite (l : PrimeGeFive) :
    (S1312SelectedBadPlace l).1 = NumberFieldPlace.finite
      (S1312SelectedBadPlaceAtPrime l).val := by
  rw [S1312SelectedBadPlaceAtPrime_val]
  exact S1312SelectedBadPlace_val l

/-- The general finite-selected-place instance, at its own computed rational
prime.  This maps every finite selected place (not only the bad one) to the
corresponding `FinitePlaceAtPrime`. -/
noncomputable def S1312SelectedFiniteAtOwnPrime (l : PrimeGeFive)
    (x : Selected (S1280Selection l))
    (hx : NumberFieldPlace.IsFinite x.1) :
    FinitePlaceAtPrime (S1280Arithmetic l).K
      (completionRationalPrime (selectedFinitePlace hx)).val :=
  ⟨selectedFinitePlace hx, rfl⟩

@[simp] theorem S1312SelectedFiniteAtOwnPrime_val (l : PrimeGeFive)
    (x : Selected (S1280Selection l))
    (hx : NumberFieldPlace.IsFinite x.1) :
    (S1312SelectedFiniteAtOwnPrime l x hx).val =
      selectedFinitePlace hx := rfl

/-- The selected bad place attached to an arbitrary bad index. -/
noncomputable def S1312BadToSelected (l : PrimeGeFive)
    (_b : Bad (S1280Selection l)) : Selected (S1280Selection l) :=
  S1312SelectedBadPlace l

theorem S1312BadToSelected_spec (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) :
    (S1312BadToSelected l b).1 = NumberFieldPlace.finite
      (S1312BadPlaceAtPrime l b).val := by
  rw [S1312BadToSelected, S1312BadPlaceAtPrime_val]
  exact S1312SelectedBadPlace_val l

/-! ## 2. The actual local field and arithmetic local group -/

/-- The Gaussian place index of the bridged bad place. -/
noncomputable def S1312BadPlaceIndex (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) : GaussianPlaceIndex :=
  finiteGaussianPlace (S1312BadPlaceAtPrime l b).val.maximalIdeal

/-- The actual local field `K_v` at the bridged place: the adic completion of
`Q(i)`. -/
noncomputable def S1312BadLocalField (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) : Type :=
  placeLocalField (S1312BadPlaceIndex l b)

noncomputable instance S1312BadLocalFieldField (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) : Field (S1312BadLocalField l b) :=
  placeLocalFieldField (S1312BadPlaceIndex l b)

/-- The local field is exactly `Completion` of the bridged finite place. -/
theorem S1312BadLocalField_eq_completion (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) :
    S1312BadLocalField l b = Completion (S1312BadPlaceAtPrime l b).val := rfl

/-- The actual arithmetic local Galois group `G_v` at the bridged place. -/
noncomputable def S1312BadArithmeticGalois (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) : ProfiniteGrp.{0} :=
  placeArithmeticGalois (S1312BadPlaceIndex l b)

/-- `G_v` is the absolute Galois group of the actual local field `K_v`. -/
theorem S1312BadArithmeticGalois_eq (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) :
    S1312BadArithmeticGalois l b =
      Iut.AbsoluteGaloisProfinite (S1312BadLocalField l b) := rfl

/-- The certified arithmetic anabelioid `B(G_v)` at the bridged place. -/
noncomputable def S1312BadArithmeticAnabelioid (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) : Iut.EtaleFundamentalGroup.{0} :=
  placeArithmeticAnabelioid (S1312BadPlaceIndex l b)

/-- The fundamental group of `B(G_v)` is the actual arithmetic local Galois
group `G_v`. -/
theorem S1312BadArithmeticAnabelioid_group (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) :
    (S1312BadArithmeticAnabelioid l b).group = S1312BadArithmeticGalois l b := rfl

/-- The actual local unit group at the bridged place.  This is an actual local
group, but it is not the curve-side group Pi_Xv/Pi_Cv of Definition 3.1(e). -/
noncomputable def S1312BadLocalUnits (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) : Type :=
  (S1312BadLocalField l b)ˣ

noncomputable instance S1312BadLocalUnitsGroup (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) : Group (S1312BadLocalUnits l b) :=
  inferInstanceAs (Group (S1312BadLocalField l b)ˣ)

/-- The actual base-changed elliptic curve over the concrete Gaussian local
field.  This is the curve field of the local source data, not an orbicurve and
not a curve-side fundamental group. -/
noncomputable def S1312ConcreteLocalCurve (l : PrimeGeFive) :
    PuncturedEllipticCurve (Completion (concreteGaussianFivePlace)) :=
  sourceFiniteLocalCurve (l := l) (S1280Arithmetic l) concreteGaussianFivePlace

/-- The concrete local curve is the existing actual base change
`sourceFiniteLocalCurve`. -/
theorem S1312ConcreteLocalCurve_eq (l : PrimeGeFive) :
    S1312ConcreteLocalCurve l =
      sourceFiniteLocalCurve (l := l) (S1280Arithmetic l)
        concreteGaussianFivePlace := rfl

/-- The actual local curve at the bridged bad place.  Its type is
`PuncturedEllipticCurve` over the completion at the bridged place; no
orbicurve structure or etale fundamental group is added. -/
noncomputable def S1312BadLocalCurve (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) :
    PuncturedEllipticCurve (Completion (S1312BadPlaceAtPrime l b).val) :=
  S1312ConcreteLocalCurve l

/-- The bad-place local curve is the concrete local curve (the bridged place is
the concrete Gaussian place). -/
theorem S1312BadLocalCurve_eq_concrete (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) :
    S1312BadLocalCurve l b = S1312ConcreteLocalCurve l := rfl

/-! ## 3. The bundled actual place bridge -/

/-- The actual S1280 D6/D7b place bridge: bad place and selected bad place to
`FinitePlaceAtPrime`, the selected bad place inside the D7a carrier, the
actual local field, the actual arithmetic local Galois group, and the certified
arithmetic anabelioid.  The structure contains no curve-side local group and no
orbicurve. -/
structure S1312PlaceBridge (l : PrimeGeFive) where
  badToPrime : Bad (S1280Selection l) →
    FinitePlaceAtPrime (S1280Arithmetic l).Fmod 5
  badToPrime_spec : ∀ b, b.1 = (badToPrime b).val
  selectedBad : Selected (S1280Selection l)
  selectedBad_val :
    selectedBad.1 = NumberFieldPlace.finite (concreteGaussianFivePlace)
  selectedBadToPrime : FinitePlaceAtPrime (S1280Arithmetic l).K 5
  selectedBadToPrime_val :
    selectedBadToPrime.val = concreteGaussianFivePlace
  localField : Bad (S1280Selection l) → Type
  localField_eq_completion :
    ∀ b, localField b = Completion (badToPrime b).val
  arithmeticGalois : Bad (S1280Selection l) → ProfiniteGrp.{0}
  arithmeticAnabelioid :
    Bad (S1280Selection l) → Iut.EtaleFundamentalGroup.{0}

/-- The bridge constructed above from the actual S1280 data. -/
noncomputable def S1312PlaceBridgeActual (l : PrimeGeFive) :
    S1312PlaceBridge l where
  badToPrime := S1312BadPlaceAtPrime l
  badToPrime_spec := S1312BadPlaceAtPrime_spec l
  selectedBad := S1312SelectedBadPlace l
  selectedBad_val := S1312SelectedBadPlace_val l
  selectedBadToPrime := S1312SelectedBadPlaceAtPrime l
  selectedBadToPrime_val := S1312SelectedBadPlaceAtPrime_val l
  localField := S1312BadLocalField l
  localField_eq_completion := fun _ => rfl
  arithmeticGalois := S1312BadArithmeticGalois l
  arithmeticAnabelioid := S1312BadArithmeticAnabelioid l

/-- The arithmetic local Galois component of the actual bridge is the absolute
Galois group of the actual local field. -/
theorem S1312PlaceBridgeActual_arithmeticGalois_eq (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) :
    (S1312PlaceBridgeActual l).arithmeticGalois b =
      Iut.AbsoluteGaloisProfinite (S1312BadLocalField l b) := rfl

/-- The anabelioid component of the actual bridge has the arithmetic local
Galois group as its fundamental group. -/
theorem S1312PlaceBridgeActual_arithmeticAnabelioid_group (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) :
    ((S1312PlaceBridgeActual l).arithmeticAnabelioid b).group =
      (S1312PlaceBridgeActual l).arithmeticGalois b := rfl

/-! ## 4. Exact first fields of D6 and D7b -/

/-- The exact D6 object: the missing nondegenerate etale-stack geometric
realization.  No inhabitant is constructed. -/
abbrev S1312D6Requirement (l : PrimeGeFive) : Type 1 :=
  MissingD6GeometricRealization (S1280Arithmetic l).F

/-- The first field of the D6 requirement (the actual curve) is the S1280
curve.  This field is actual, not a new choice. -/
abbrev S1312D6ActualCurve (l : PrimeGeFive) :
    PuncturedEllipticCurve (S1280Arithmetic l).F :=
  (S1280Arithmetic l).curve

theorem S1312D6ActualCurve_eq (l : PrimeGeFive) :
    S1312D6ActualCurve l = (S1280Arithmetic l).curve := rfl

/-- The first D6 field not determined by the concrete Gaussian data: the etale
stack fiber. -/
abbrev S1312D6FirstMissingField (l : PrimeGeFive) : Type 1 :=
  Iut.EtaleStackPseudofunctor (S1280Arithmetic l).F

/-- Any D6 requirement supplies the first missing field; no inhabitant of the
requirement itself is asserted. -/
noncomputable def S1312D6FiberOfRequirement (l : PrimeGeFive)
    (D : S1312D6Requirement l) : S1312D6FirstMissingField l :=
  D.fiber

/-- The canonical D7a place-section layer for the S1280 arithmetic input. -/
abbrev S1312D7Layer (l : PrimeGeFive) :
    SourceValuationSectionLayer (S1280Arithmetic l) :=
  SourceValuationSectionLayer.canonical (S1280Arithmetic l)

/-- The selected bad place as a point of the D7b carrier domain. -/
noncomputable def S1312SelectedBadPlaceD7 (l : PrimeGeFive) :
    (S1312D7Layer l).valuationCarrier :=
  S1312SelectedBadPlace l

/-- Exact D7b object: the local-group supply over the canonical D7a layer.
No inhabitant is constructed. -/
abbrev S1312D7bRequirement (l : PrimeGeFive) : Type 1 :=
  D7LocalGroupSectionSupply.{0, 0} (S1312D7Layer l)

/-- The exact first field of D7b: the local-group carrier family over the
actual D7a carrier.  This is the first ray of the curve-side Pi_Xv/Pi_Cv data;
the arithmetic group `G_v` is not it. -/
abbrev S1312D7bFirstField (l : PrimeGeFive) : Type 1 :=
  (S1312D7Layer l).valuationCarrier → Type

/-- Any D7b supply projects to its first field. -/
noncomputable def S1312D7bFirstFieldOfSupply (l : PrimeGeFive)
    (G : S1312D7bRequirement l) : S1312D7bFirstField l :=
  G.localGroupCarrier

/-- The first D7b field is necessary for any supply. -/
theorem S1312D7bFirstField_needed (l : PrimeGeFive)
    (G : S1312D7bRequirement l) : Nonempty (S1312D7bFirstField l) :=
  ⟨S1312D7bFirstFieldOfSupply l G⟩

/-- The domain of the D7b first field is actual and nonempty: it contains the
selected bad place. -/
theorem S1312D7bFirstField_domain_nonempty (l : PrimeGeFive) :
    Nonempty (S1312D7Layer l).valuationCarrier :=
  ⟨S1312SelectedBadPlaceD7 l⟩

/-- The selected bad place as a D7 carrier point is the finite place at the
bridge. -/
theorem S1312SelectedBadPlaceD7_val (l : PrimeGeFive) :
    (S1312SelectedBadPlaceD7 l).1 = NumberFieldPlace.finite
      (S1312SelectedBadPlaceAtPrime l).val :=
  S1312SelectedBadPlaceAtPrime_eq_finite l

/-! ## 5. Axiom footprint -/

#print axioms S1312BadPlaceAtPrime
#print axioms S1312BadAtOwnPrime
#print axioms S1312BadPlaceAtPrime_eq_ownPrime
#print axioms S1312BadPlaceAtPrime_range
#print axioms S1312SelectedBadPlace
#print axioms S1312SelectedFiniteAtOwnPrime
#print axioms S1312SelectedBadPlaceAtPrime
#print axioms S1312PlaceBridgeActual
#print axioms S1312BadArithmeticGalois
#print axioms S1312BadArithmeticAnabelioid
#print axioms S1312BadLocalUnits
#print axioms S1312BadLocalCurve
#print axioms S1312D6FiberOfRequirement
#print axioms S1312D7bFirstFieldOfSupply
#print axioms S1312D7bFirstField_domain_nonempty

end LeanFormal.IUT.XiFPaper.S1312D7LocalGroupActual

end
