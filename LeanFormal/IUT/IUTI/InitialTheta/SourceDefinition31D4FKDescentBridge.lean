import LeanFormal.IUT.Audit.Status
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlacePartitionReduction
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlaceQParameterUniformization
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31D4TateQIdentification

/-!
# D4 reduction pass: the F-to-K identification descent bridge

Source: IUT I, Definition 3.1(b) (corpus lines 3142-3157: the bad moduli set
`Vbad_mod` is a nonempty set of nonarchimedean valuations of `Fmod` of odd
residue characteristic such that `X_F` has bad, i.e. multiplicative,
reduction at the elements of `V(F)` lying over it; `V(F)^bad` is the fibre
of `V(F) -> Vmod` over `Vbad_mod`), Definition 3.1(c) (corpus lines
3180-3184: `l` is prime to the residue characteristics of the elements of
`Vbad_mod` and to the orders of the q-parameters of `E_F` at the primes of
`V(F)^bad`), Definition 3.1(e) (corpus lines 3216-3226: the section
`V -> Vmod` of `V(K) -> Vmod`), and Example 3.2(iv) (corpus lines
3701-3726: the q-parameter `q_v` of `E_v` over `K_v` and its `2l`-th root,
determined only up to a `mu_{2l}`-multiple).

This leaf evaluates the three descent routes for the frozen D4 boundary
`TateQIdentificationStatement` (see
`SourceDefinition31D4TateQIdentification.lean`), which compares the Tate
card order at an `A.F`-place with the DVR proxy order at the
section-chosen `A.K`-place above its moduli place:

* Direct route (unconditional fragments): the `A.F`-shadow
  `fkDescentShadow` of the section lift always lies over the same moduli
  place (`fkDescentShadow_comap`); the proxy order is fibre-constant by
  construction (`fkDescent_badPlaceQCandidate_order_fiber`); and the only
  cross-field order transfer in the tree is the `A.F`-to-`A.K`
  ramification scaling at the shadow
  (`fkDescent_order_map_sectionFiniteLift`, the `order_map`
  instantiation). The naive place-identity hypothesis of the direct route
  is recorded, not assumed, as `FKDescentSectionFiberCollapse`.

* Conditional route (reduced forms, explicitly labelled as such; no
  instance asserted): the frozen identification is equivalent to the
  conjunction of the frozen fibre-uniformity statement and the frozen
  shadow statement, in both the `A.F`-place-indexed and the
  moduli-indexed form. The normalisation-aware scaled variants record the
  ramification factor produced by `order_map`
  (`FKDescentScaledShadowStatement`,
  `FKDescentScaledIdentificationStatement`) together with the upward-map
  realisation form (`fkDescent_scaledShadow_iff_mapRealization`); at
  ramification index one the scaled forms collapse to the equality forms.

* Independence route (unconditional): candidate orders at a fixed
  completed place are unbounded (`exists_order_gt`), so the order of the
  `Classical.choice`-defined section proxy is not determined by its
  carrier; the identification is genuine extra content.

Boundary: no forbidden placeholders or new axioms; nothing here closes a gate, constructs
an instance of `BadPlaceTateUniformizationCards`, or proves any paper
statement about q-parameters of curves. The tree has no Galois action on
finite places and no norm descent for q-candidates; together with the
choice-opacity of `badPlaceQCandidate` these are the API-level reasons the
direct route stops. The order-level fibre uniformity frozen here is the
same shape as the reduction-type fibre uniformity recorded in subgap (i)
of `IUT-I.definition-3.1-D3-arithmetic-bad-moduli-gap` and is flagged for
deduplication.
-/

namespace LeanFormal.IUT

noncomputable section

universe u

namespace NumberFieldFinitePlace.FinitePlaceQCandidate

variable {K : Type u} [Field K] [NumberField K]

/-- Positive powers of a q-candidate realise arbitrarily large orders: for
any bound `c` there is a valuation-theoretic q-candidate at the given
completed finite place whose order exceeds `c`. The order of a candidate is
therefore not determined by the place, and the `Classical.choice`-defined
section proxy of the D4 line carries no derivable order value beyond
positivity. -/
theorem exists_order_gt (place : NumberField.FinitePlace K) (c : Nat) :
    ∃ parameter : FinitePlaceQCandidate place, c < parameter.order := by
  obtain ⟨parameter⟩ := finitePlaceQCandidate_nonempty place
  refine ⟨parameter.pow (c + 1) (Nat.succ_pos c), ?_⟩
  rw [order_pow]
  have hle : c + 1 ≤ (c + 1) * parameter.order := by
    have h1 : 1 ≤ parameter.order := Nat.succ_le_of_lt parameter.order_pos
    calc c + 1 = (c + 1) * 1 := (Nat.mul_one (c + 1)).symm
      _ ≤ (c + 1) * parameter.order := Nat.mul_le_mul (le_refl (c + 1)) h1
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self c) hle

end NumberFieldFinitePlace.FinitePlaceQCandidate

namespace InitialThetaSource

namespace PlacePartitionReduction

variable {l : PrimeGeFive}
variable {A : InitialThetaArithmeticData.{u} l}

/-! ## Direct route: shadow, fibre constancy, and the only cross-field
order transfer -/

/-- The `A.F`-shadow of the section-chosen `A.K`-place above a moduli place
`p`: the finite place of `A.F` obtained by contracting `sectionFiniteLift P p`
along `A.F -> A.K`. The section selects one `A.K`-place per moduli place, so
its shadow is the single `A.F`-place that the section promotes to the `A.F`
level; a general `A.F`-place over `p` need not coincide with it. -/
def fkDescentShadow (P : SourcePlaceSelection A)
    (p : NumberField.FinitePlace A.Fmod) : NumberField.FinitePlace A.F :=
  NumberFieldFinitePlace.comap (k := A.F) (sectionFiniteLift P p)

/-- The shadow of the section lift always lies over the same moduli place:
the composite `A.Fmod -> A.F -> A.K` contraction of the section lift is the
identity on moduli places. -/
theorem fkDescentShadow_comap (P : SourcePlaceSelection A)
    (p : NumberField.FinitePlace A.Fmod) :
    NumberFieldFinitePlace.comap (k := A.Fmod) (fkDescentShadow P p) = p := by
  simp only [fkDescentShadow, NumberFieldFinitePlace.comap_comap,
    sectionFiniteLift_comap]

/-- Membership transport: the shadow of a bad moduli place is a bad
`A.F`-place. -/
theorem fkDescentShadow_mem (P : SourcePlaceSelection A)
    (p : NumberField.FinitePlace A.Fmod) (hp : p ∈ P.V_mod_bad) :
    NumberFieldFinitePlace.comap (k := A.Fmod) (fkDescentShadow P p) ∈
      P.V_mod_bad := by
  rw [fkDescentShadow_comap]
  exact hp

/-- The shadow depends only on the moduli place: places of `A.F` with the
same restriction to `A.Fmod` have the same shadow. -/
theorem fkDescentShadow_congr_of_comap_eq (P : SourcePlaceSelection A)
    {w w' : NumberField.FinitePlace A.F}
    (h : NumberFieldFinitePlace.comap (k := A.Fmod) w =
      NumberFieldFinitePlace.comap (k := A.Fmod) w') :
    fkDescentShadow P (NumberFieldFinitePlace.comap (k := A.Fmod) w) =
      fkDescentShadow P (NumberFieldFinitePlace.comap (k := A.Fmod) w') := by
  rw [h]

/-- The section proxy depends only on the moduli place: two `A.F`-places
with the same restriction to `A.Fmod` carry the same `Bad` index, hence the
same chosen proxy candidate, hence the same proxy order. This is the
fibre-constancy of the right-hand side of the frozen identification. -/
theorem fkDescent_badPlaceQCandidate_order_fiber (P : SourcePlaceSelection A)
    {w w' : NumberField.FinitePlace A.F}
    (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad)
    (hw' : NumberFieldFinitePlace.comap (k := A.Fmod) w' ∈ P.V_mod_bad)
    (h : NumberFieldFinitePlace.comap (k := A.Fmod) w =
      NumberFieldFinitePlace.comap (k := A.Fmod) w') :
    (badPlaceQCandidate P
        ⟨NumberFieldFinitePlace.comap (k := A.Fmod) w, hw⟩).order =
      (badPlaceQCandidate P
        ⟨NumberFieldFinitePlace.comap (k := A.Fmod) w', hw'⟩).order :=
  congrArg (fun b : Bad P => (badPlaceQCandidate P b).order) (Subtype.ext h)

/-- Card orders are invariant under place transport: the card at a bad
`A.F`-place depends on the place only through its membership proof. This is
the transport form used by the naive place-identity route below. -/
theorem fkDescent_cardOrder_congr_place (P : SourcePlaceSelection A)
    (C : PlaceQParameterUniformization.BadPlaceTateUniformizationCards P)
    {w w' : NumberField.FinitePlace A.F}
    (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad)
    (hw' : NumberFieldFinitePlace.comap (k := A.Fmod) w' ∈ P.V_mod_bad)
    (hww' : w = w') :
    (C.parameter w hw).order = (C.parameter w' hw').order := by
  subst hww'
  rfl

/-- The ramification index of the section-chosen `A.K`-place over its
`A.F`-shadow: the scale factor between the normalised valuations at the two
levels, i.e. the factor produced by the only cross-field order transfer
available in the tree. -/
def fkDescentSectionRamificationIndex (P : SourcePlaceSelection A)
    (p : NumberField.FinitePlace A.Fmod) : Nat :=
  (fkDescentShadow P p).maximalIdeal.asIdeal.ramificationIdx'
    (sectionFiniteLift P p).maximalIdeal.asIdeal

/-- Upward `A.F`-to-`A.K` q-order transfer at the section place: a
candidate at the shadow place maps to the section-chosen `A.K`-place with
order scaled by `fkDescentSectionRamificationIndex`. This is the `order_map`
instantiation at the section pair; the transfer starts from a candidate at
the shadow place, not from the Tate card of an arbitrary `A.F`-place in the
fibre. -/
theorem fkDescent_order_map_sectionFiniteLift (P : SourcePlaceSelection A)
    (p : NumberField.FinitePlace A.Fmod)
    (parameter : NumberFieldFinitePlace.FinitePlaceQCandidate
      (fkDescentShadow P p)) :
    (NumberFieldFinitePlace.FinitePlaceQCandidate.map (k := A.F)
        (sectionFiniteLift P p) parameter).order =
      fkDescentSectionRamificationIndex P p * parameter.order :=
  NumberFieldFinitePlace.FinitePlaceQCandidate.order_map (k := A.F)
    (sectionFiniteLift P p) parameter

/-- The naive place-identity hypothesis of the direct route: every bad
`A.F`-place is the shadow of its own section-chosen `A.K`-place. This is
NOT asserted, no instance is provided, and it is not derivable in the tree:
a moduli fibre of the contraction `V(A.F) -> V(A.Fmod)` may contain several
`A.F`-places while the section selects one `A.K`-place per moduli place. The
statement is recorded only to locate the obstruction of the direct route;
the fibre-uniformity statement below is the honest replacement. -/
def FKDescentSectionFiberCollapse (P : SourcePlaceSelection A) : Prop :=
  ∀ (w : NumberField.FinitePlace A.F)
    (_hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
    fkDescentShadow P (NumberFieldFinitePlace.comap (k := A.Fmod) w) = w

/-! ## Conditional route: frozen reduced forms and assembly -/

/-- Frozen fibre-uniformity statement for the D4 Tate cards: the parameter
orders of `BadPlaceTateUniformizationCards` are constant along the fibres of
the contraction `V(A.F) -> V(A.Fmod)` over the bad moduli set. Reduced form;
no instance asserted. This is the order-level companion of the
reduction-type fibre uniformity recorded in subgap (i) of
`IUT-I.definition-3.1-D3-arithmetic-bad-moduli-gap`. -/
def FKDescentFiberUniformityStatement (P : SourcePlaceSelection A)
    (C : PlaceQParameterUniformization.BadPlaceTateUniformizationCards P) :
    Prop :=
  ∀ (w w' : NumberField.FinitePlace A.F)
    (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad)
    (hw' : NumberFieldFinitePlace.comap (k := A.Fmod) w' ∈ P.V_mod_bad),
    NumberFieldFinitePlace.comap (k := A.Fmod) w =
      NumberFieldFinitePlace.comap (k := A.Fmod) w' →
    (C.parameter w hw).order = (C.parameter w' hw').order

/-- Frozen shadow statement: at the section-selected `A.F`-shadow of each
bad `A.F`-place, the card order equals the proxy order at the
section-selected `A.K`-place above the same moduli place. Reduced form of
the frozen `TateQIdentificationStatement`; no instance asserted. -/
def FKDescentShadowStatement (P : SourcePlaceSelection A)
    (C : PlaceQParameterUniformization.BadPlaceTateUniformizationCards P) :
    Prop :=
  ∀ (w : NumberField.FinitePlace A.F)
    (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
    (C.parameter
        (fkDescentShadow P (NumberFieldFinitePlace.comap (k := A.Fmod) w))
        (fkDescentShadow_mem P
          (NumberFieldFinitePlace.comap (k := A.Fmod) w) hw)).order =
      (badPlaceQCandidate P
        ⟨NumberFieldFinitePlace.comap (k := A.Fmod) w, hw⟩).order

/-- Frozen moduli-indexed shadow statement: the same comparison, indexed by
the bad moduli places directly, with no `A.F`-place quantifier. -/
def FKDescentModuliShadowStatement (P : SourcePlaceSelection A)
    (C : PlaceQParameterUniformization.BadPlaceTateUniformizationCards P) :
    Prop :=
  ∀ (p : NumberField.FinitePlace A.Fmod) (hp : p ∈ P.V_mod_bad),
    (C.parameter (fkDescentShadow P p) (fkDescentShadow_mem P p hp)).order =
      (badPlaceQCandidate P ⟨p, hp⟩).order

/-- Frozen normalisation-aware scaled shadow statement: the proxy order at
the section place equals the ramification index of the section place over
its `A.F`-shadow times the card order at the shadow. This is the shape that
the upward transfer `order_map` produces; at ramification index one it is
`FKDescentShadowStatement`. Reduced form; no instance asserted. -/
def FKDescentScaledShadowStatement (P : SourcePlaceSelection A)
    (C : PlaceQParameterUniformization.BadPlaceTateUniformizationCards P) :
    Prop :=
  ∀ (w : NumberField.FinitePlace A.F)
    (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
    (badPlaceQCandidate P
        ⟨NumberFieldFinitePlace.comap (k := A.Fmod) w, hw⟩).order =
      fkDescentSectionRamificationIndex P
          (NumberFieldFinitePlace.comap (k := A.Fmod) w) *
        (C.parameter
          (fkDescentShadow P (NumberFieldFinitePlace.comap (k := A.Fmod) w))
          (fkDescentShadow_mem P
            (NumberFieldFinitePlace.comap (k := A.Fmod) w) hw)).order

/-- Frozen normalisation-aware scaled identification statement: the scaled
comparison at the `A.F`-place itself, obtained from the scaled shadow
statement on fibre-uniform cards. Reduced form; no instance asserted. -/
def FKDescentScaledIdentificationStatement (P : SourcePlaceSelection A)
    (C : PlaceQParameterUniformization.BadPlaceTateUniformizationCards P) :
    Prop :=
  ∀ (w : NumberField.FinitePlace A.F)
    (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
    (badPlaceQCandidate P
        ⟨NumberFieldFinitePlace.comap (k := A.Fmod) w, hw⟩).order =
      fkDescentSectionRamificationIndex P
          (NumberFieldFinitePlace.comap (k := A.Fmod) w) *
        (C.parameter w hw).order

/-- Frozen upward-map realisation statement: for every bad `A.F`-place there
is a candidate at its shadow whose order equals the card order at the shadow
and whose image under the upward `map` realises the proxy order. Reduced
form; no instance asserted. -/
def FKDescentMapRealizationStatement (P : SourcePlaceSelection A)
    (C : PlaceQParameterUniformization.BadPlaceTateUniformizationCards P) :
    Prop :=
  ∀ (w : NumberField.FinitePlace A.F)
    (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
    ∃ gamma : NumberFieldFinitePlace.FinitePlaceQCandidate
        (fkDescentShadow P (NumberFieldFinitePlace.comap (k := A.Fmod) w)),
      (badPlaceQCandidate P
          ⟨NumberFieldFinitePlace.comap (k := A.Fmod) w, hw⟩).order =
        (NumberFieldFinitePlace.FinitePlaceQCandidate.map (k := A.F)
          (sectionFiniteLift P
            (NumberFieldFinitePlace.comap (k := A.Fmod) w)) gamma).order ∧
      gamma.order =
        (C.parameter
          (fkDescentShadow P (NumberFieldFinitePlace.comap (k := A.Fmod) w))
          (fkDescentShadow_mem P
            (NumberFieldFinitePlace.comap (k := A.Fmod) w) hw)).order

/-- Assembly: fibre uniformity together with the shadow statement
reconstructs the frozen identification. -/
theorem fkDescent_tateQIdentification_of_fiberUniformity
    (P : SourcePlaceSelection A)
    (C : PlaceQParameterUniformization.BadPlaceTateUniformizationCards P)
    (hF : FKDescentFiberUniformityStatement P C)
    (hS : FKDescentShadowStatement P C) :
    TateQIdentificationStatement P C := by
  intro w hw
  refine
    (hF w (fkDescentShadow P (NumberFieldFinitePlace.comap (k := A.Fmod) w))
      hw
      (fkDescentShadow_mem P
        (NumberFieldFinitePlace.comap (k := A.Fmod) w) hw)
      (fkDescentShadow_comap P
        (NumberFieldFinitePlace.comap (k := A.Fmod) w)).symm).trans
      (hS w hw)

/-- The frozen identification implies fibre uniformity of the card orders
along the moduli fibres: the right-hand side of the identification is
fibre-constant by construction. -/
theorem fkDescent_fiberUniformity_of_tateQIdentification
    (P : SourcePlaceSelection A)
    (C : PlaceQParameterUniformization.BadPlaceTateUniformizationCards P)
    (h : TateQIdentificationStatement P C) :
    FKDescentFiberUniformityStatement P C := by
  intro w w' hw hw' hcomap
  rw [h w hw, h w' hw']
  exact congrArg (fun b : Bad P => (badPlaceQCandidate P b).order)
    (Subtype.ext hcomap)

/-- The frozen identification implies the shadow statement, using the
fibre-constancy of the proxy. -/
theorem fkDescent_shadowStatement_of_tateQIdentification
    (P : SourcePlaceSelection A)
    (C : PlaceQParameterUniformization.BadPlaceTateUniformizationCards P)
    (h : TateQIdentificationStatement P C) :
    FKDescentShadowStatement P C := by
  intro w hw
  have hsh :=
    h (fkDescentShadow P (NumberFieldFinitePlace.comap (k := A.Fmod) w))
      (fkDescentShadow_mem P
        (NumberFieldFinitePlace.comap (k := A.Fmod) w) hw)
  rw [hsh]
  exact congrArg (fun b : Bad P => (badPlaceQCandidate P b).order)
    (Subtype.ext (fkDescentShadow_comap P
      (NumberFieldFinitePlace.comap (k := A.Fmod) w)))

/-- The frozen identification boundary is equivalent to the conjunction of
the frozen fibre-uniformity statement and the frozen shadow statement: the
whole content of the `forall w` identification quantifier reduces to (i)
order-uniformity of the card along the moduli fibres and (ii) a single
comparison at the section-chosen shadow of each bad moduli place. -/
theorem fkDescent_tateQIdentification_iff_fiberUniformity_and_shadow
    (P : SourcePlaceSelection A)
    (C : PlaceQParameterUniformization.BadPlaceTateUniformizationCards P) :
    TateQIdentificationStatement P C ↔
      FKDescentFiberUniformityStatement P C ∧
        FKDescentShadowStatement P C :=
  ⟨fun h => ⟨fkDescent_fiberUniformity_of_tateQIdentification P C h,
      fkDescent_shadowStatement_of_tateQIdentification P C h⟩,
    fun h => fkDescent_tateQIdentification_of_fiberUniformity P C h.1 h.2⟩

/-- The shadow statement is equivalent to its moduli-indexed form. -/
theorem fkDescent_shadowStatement_iff_moduliShadow
    (P : SourcePlaceSelection A)
    (C : PlaceQParameterUniformization.BadPlaceTateUniformizationCards P) :
    FKDescentShadowStatement P C ↔ FKDescentModuliShadowStatement P C := by
  constructor
  · intro hS p hp
    obtain ⟨w, hw⟩ := moduliPlace_fiber_nonempty p
    subst hw
    exact hS w hp
  · intro hM w hw
    exact hM (NumberFieldFinitePlace.comap (k := A.Fmod) w) hw

/-- The frozen identification boundary in its consumer form: fibre
uniformity of the card orders together with the modulus-indexed shadow
statement. -/
theorem fkDescent_tateQIdentification_iff_fiberUniformity_and_moduliShadow
    (P : SourcePlaceSelection A)
    (C : PlaceQParameterUniformization.BadPlaceTateUniformizationCards P) :
    TateQIdentificationStatement P C ↔
      FKDescentFiberUniformityStatement P C ∧
        FKDescentModuliShadowStatement P C := by
  constructor
  · intro hI
    obtain ⟨hF, hS⟩ :=
      (fkDescent_tateQIdentification_iff_fiberUniformity_and_shadow P C).mp hI
    exact ⟨hF, (fkDescent_shadowStatement_iff_moduliShadow P C).mp hS⟩
  · intro h
    exact (fkDescent_tateQIdentification_iff_fiberUniformity_and_shadow P C).mpr
      ⟨h.1, (fkDescent_shadowStatement_iff_moduliShadow P C).mpr h.2⟩

/-- On the naive place-identity hypothesis the shadow statement and the
frozen identification coincide: this locates the direct route's obstruction
in the place-identity step alone. The hypothesis is not asserted anywhere;
it is recorded for the route evaluation. -/
theorem fkDescent_shadowStatement_iff_tateQIdentification_of_collapse
    (P : SourcePlaceSelection A)
    (C : PlaceQParameterUniformization.BadPlaceTateUniformizationCards P)
    (hcollapse : FKDescentSectionFiberCollapse P) :
    FKDescentShadowStatement P C ↔ TateQIdentificationStatement P C := by
  constructor
  · intro hS w hw
    exact (fkDescent_cardOrder_congr_place P C
      (fkDescentShadow_mem P
        (NumberFieldFinitePlace.comap (k := A.Fmod) w) hw)
      hw (hcollapse w hw)).symm.trans (hS w hw)
  · intro hI w hw
    exact (fkDescent_cardOrder_congr_place P C
      (fkDescentShadow_mem P
        (NumberFieldFinitePlace.comap (k := A.Fmod) w) hw)
      hw (hcollapse w hw)).trans (hI w hw)

/-- On fibre-uniform cards the scaled shadow statement assembles the scaled
comparison at every bad `A.F`-place. -/
theorem fkDescent_scaledIdentification_of_fiberUniformity
    (P : SourcePlaceSelection A)
    (C : PlaceQParameterUniformization.BadPlaceTateUniformizationCards P)
    (hF : FKDescentFiberUniformityStatement P C)
    (hS : FKDescentScaledShadowStatement P C) :
    FKDescentScaledIdentificationStatement P C := by
  intro w hw
  rw [hS w hw]
  exact congrArg
    (fun n => fkDescentSectionRamificationIndex P
      (NumberFieldFinitePlace.comap (k := A.Fmod) w) * n)
    (hF (fkDescentShadow P (NumberFieldFinitePlace.comap (k := A.Fmod) w)) w
      (fkDescentShadow_mem P
        (NumberFieldFinitePlace.comap (k := A.Fmod) w) hw) hw
      (fkDescentShadow_comap P
        (NumberFieldFinitePlace.comap (k := A.Fmod) w)))

/-- At ramification index one everywhere, the scaled identification is the
frozen identification. -/
theorem fkDescent_tateQIdentification_iff_scaled_of_ramificationIdx_eq_one
    (P : SourcePlaceSelection A)
    (C : PlaceQParameterUniformization.BadPlaceTateUniformizationCards P)
    (hone : ∀ p : NumberField.FinitePlace A.Fmod,
      fkDescentSectionRamificationIndex P p = 1) :
    TateQIdentificationStatement P C ↔
      FKDescentScaledIdentificationStatement P C := by
  constructor
  · intro hI w hw
    rw [← hI w hw, hone (NumberFieldFinitePlace.comap (k := A.Fmod) w),
      one_mul]
  · intro hS w hw
    rw [hS w hw, hone (NumberFieldFinitePlace.comap (k := A.Fmod) w),
      one_mul]

/-- At ramification index one everywhere, the scaled shadow statement is
the shadow statement. -/
theorem fkDescent_shadowStatement_of_scaled_of_ramificationIdx_eq_one
    (P : SourcePlaceSelection A)
    (C : PlaceQParameterUniformization.BadPlaceTateUniformizationCards P)
    (hone : ∀ p : NumberField.FinitePlace A.Fmod,
      fkDescentSectionRamificationIndex P p = 1)
    (hS : FKDescentScaledShadowStatement P C) :
    FKDescentShadowStatement P C := by
  intro w hw
  have h := hS w hw
  rw [hone (NumberFieldFinitePlace.comap (k := A.Fmod) w), one_mul] at h
  exact h.symm

/-- The scaled shadow statement is exactly the statement that the proxy
order is realised, at the level of orders, by the upward map of a candidate
at the shadow whose order is the card order there. -/
theorem fkDescent_scaledShadow_iff_mapRealization
    (P : SourcePlaceSelection A)
    (C : PlaceQParameterUniformization.BadPlaceTateUniformizationCards P) :
    FKDescentScaledShadowStatement P C ↔
      FKDescentMapRealizationStatement P C := by
  constructor
  · intro hS w hw
    refine ⟨C.parameter
        (fkDescentShadow P (NumberFieldFinitePlace.comap (k := A.Fmod) w))
        (fkDescentShadow_mem P
          (NumberFieldFinitePlace.comap (k := A.Fmod) w) hw), ?_, rfl⟩
    rw [fkDescent_order_map_sectionFiniteLift]
    simpa only [fkDescentSectionRamificationIndex] using hS w hw
  · intro hM w hw
    obtain ⟨gamma, hproxy, hcard⟩ := hM w hw
    have hmap := fkDescent_order_map_sectionFiniteLift P
      (NumberFieldFinitePlace.comap (k := A.Fmod) w) gamma
    exact hproxy.trans (hmap.trans (by rw [hcard]))

/-- Candidates of arbitrarily large order exist at every section lift: the
proxy order is not determined by the carrier place. -/
theorem fkDescent_sectionLift_order_unbounded (P : SourcePlaceSelection A)
    (p : NumberField.FinitePlace A.Fmod) (c : Nat) :
    ∃ parameter : NumberFieldFinitePlace.FinitePlaceQCandidate
        (sectionFiniteLift P p), c < parameter.order :=
  NumberFieldFinitePlace.FinitePlaceQCandidate.exists_order_gt
    (sectionFiniteLift P p) c

end PlacePartitionReduction

end InitialThetaSource

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- F-to-K identification descent bridge card (conditional). -/
def sourceDefinition31D4FKDescentBridge : Obligation :=
  { id := "IUT-I.definition-3.1-D4-fk-identification-descent-bridge"
    source :=
      "IUT I, Definition 3.1(b)-(c), (e) (corpus 3142-3157, 3180-3184, " ++
        "3216-3226); Example 3.2(iv) (corpus 3701-3726)"
    status := VerificationStatus.conditional
    note :=
      "Three-route evaluation of the F-to-K identification descent " ++
        "bridge for the frozen `TateQIdentificationStatement`. Proved " ++
        "unconditionally: the shadow of the section lift lies over the " ++
        "same moduli place; the proxy order is fibre-constant by " ++
        "construction; the upward transfer at the section place is the " ++
        "`order_map` scaling by the section ramification index; and the " ++
        "frozen identification is equivalent to fibre uniformity of the " ++
        "card orders together with the shadow statement (both " ++
        "place-indexed and moduli-indexed forms), with the scaled and " ++
        "upward-map-realisation variants equivalent to the scaled shadow " ++
        "statement. Unproved and frozen: " ++
        "`FKDescentFiberUniformityStatement` and " ++
        "`FKDescentShadowStatement` (no instance asserted anywhere). " ++
        "Independence fragment: candidate orders at a fixed completed " ++
        "place are unbounded, so the `Classical.choice`-defined proxy " ++
        "carries no derivable order value beyond positivity. The tree has " ++
        "no Galois action on finite places and no norm descent for " ++
        "q-candidates; the naive place-identity route is recorded as " ++
        "`FKDescentSectionFiberCollapse`, not assumed. No gate is closed, " ++
        "no `BadPlaceTateUniformizationCards` instance is constructed, " ++
        "and no Tate-curve statement is inferred."
    dependsOn :=
      [ "IUT-I.definition-3.1-D4-tate-q-identification",
        "IUT-I.definition-3.1-D4-q-order-transfer-kernel",
        "IUT-I.definition-3.1-D3-arithmetic-bad-moduli-gap" ] }

end LeanFormal.IUT.Audit
