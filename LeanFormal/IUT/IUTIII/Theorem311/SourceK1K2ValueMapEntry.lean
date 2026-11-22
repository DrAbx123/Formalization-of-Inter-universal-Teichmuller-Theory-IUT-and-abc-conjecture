import LeanFormal.IUT.IUTII.Frobenioid.PrimeStripsFrobenioidLinks
import LeanFormal.IUT.IUTIII.Theorem311.SourceK1K2Realization
import Mathlib.Tactic

/-!
  # Value-map entry into the K2 Frobenioid construction
  (run k1k2-realization-20261016, fourth leaf; Kepler REQ-2 supply/card)

  Kepler's value-group / stripping layer asks that a value map `V_K · ρv` enter
  the K2 construction anchored at `SourceK1K2Construction.lean:679` (K2 record
  fields `localFrobenioid` / `globalFrobenioid` with their realification slots,
  `SourceK1K2Construction.lean:350-385`), so that the downstream
  identifications `v((Q̄p)^×) = ℚ` and degree image `ℚ · log p` can be consumed.

  Supply shape proved in this file:

  * `frobenioidValueKernelOfValueMap`: a value homomorphism `ρv : X → Real`
    (additive over multiplication, zero at `1`) together with a transport
    invariant under `ρv` determines the whole reduced Frobenioid value kernel;
    the degree hom is forced to be `Multiplicative.ofAdd ∘ ρv`, so
    `realification = ρv` definitionally.  (Norm-log degree template already in
    the tree: `unitNormLogDegree`, `Foundations/Arithmetic/NormLog.lean:17`.)
  * `primeStripFrobenioidLinkLayerOfValueMaps`: two such value maps with aligned
    `modMap`/`MODMap` data (value equations and transport equations) form the
    link layer consumed by K2.
  * `k2FrobenioidBoundaryOfValueMaps`: the value maps reach the frozen
    `K2FrobenioidBoundary` through `k2FrobenioidBoundaryOfLinkLayer`; the
    remaining inputs are unchanged from item 28: the source realization `R`,
    the K1 vertical carrier `K`, and the four comparison alignments.

  Card (what this supply does *not* contain): the two downstream
  identifications are range statements on the value map,

  * `ValueMapRationalImage ρv` : `Set.range ρv = Set.range (ℚ → ℝ)`,
  * `ValueMapScaledRationalImage scale ρv` : the image of `scale * ρv` is
    `scale · ℚ` (the degree image `ℚ · log p` at `scale = log p`),

  and no field of `FrobenioidValueKernel`, `PrimeStripFrobenioidLinkLayer`, or
  `K2FrobenioidBoundary` constrains the range of a value map.  This is witnessed
  by `zeroValueMapKernel_not_rationalImage`: the constant-zero value map is an
  admissible kernel whose image is `{0}`.  The image statements are therefore
  additional hypotheses for the consumer (or arithmetic proved on the Kepler
  side); the only implication supplied here is
  `valueMapScaledRationalImage_of_rationalImage`.

  Status boundary: no arithmetic of `ℚ`-valued valuations, no p-adic field, and
  no identification of any concrete carrier with `(Q̄p)^×` is claimed here.
-/

set_option linter.unusedVariables false

namespace LeanFormal.IUT

universe u v ux uy

namespace K1K2Realization

noncomputable section

open Theorem311Source
open Theorem311Source.SourceHodgeTheaterBridge
open Theorem311Source.SourceDependencyChain

variable {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
variable [AddGroup Label] [Preorder Choice]

/-! ## 1. From a value map to the reduced Frobenioid value kernel -/

/-- Kepler REQ-2 entry, local form: a value homomorphism `ρv : X → Real` with a
transport invariant under `ρv` determines the reduced Frobenioid value kernel.
The degree hom is forced: `degree = Multiplicative.ofAdd ∘ ρv`; hence
`degree_realification` holds definitionally and the kernel's realification is
the given value map. -/
def frobenioidValueKernelOfValueMap {X : Type ux} [CommMonoid X]
    (ρv : X → Real) (hρv_mul : ∀ x y, ρv (x * y) = ρv x + ρv y)
    (hρv_one : ρv 1 = 0)
    (transport : X → X) (htransport : ∀ x, ρv (transport x) = ρv x) :
    FrobenioidValueKernel X where
  degree :=
    { toFun := fun x => Multiplicative.ofAdd (ρv x)
      map_one' := by
        change Multiplicative.ofAdd (ρv 1) = Multiplicative.ofAdd (0 : Real)
        rw [hρv_one]
      map_mul' := fun x y => by
        change Multiplicative.ofAdd (ρv (x * y)) =
          Multiplicative.ofAdd (ρv x) * Multiplicative.ofAdd (ρv y)
        rw [hρv_mul x y, ofAdd_add] }
  realification := ρv
  realification_mul := hρv_mul
  degree_realification := fun x => rfl
  unit := 1
  unit_realification := hρv_one
  effective := fun _ => True
  effective_proved := fun _ => trivial
  transport := transport
  transport_degree := fun x => by
    change Multiplicative.ofAdd (ρv (transport x)) = Multiplicative.ofAdd (ρv x)
    rw [htransport x]

/-- Consumption hook: the realification of the kernel built from `ρv` is `ρv`,
definitionally. -/
theorem frobenioidValueKernelOfValueMap_realification {X : Type ux} [CommMonoid X]
    (ρv : X → Real) (hρv_mul : ∀ x y, ρv (x * y) = ρv x + ρv y)
    (hρv_one : ρv 1 = 0)
    (transport : X → X) (htransport : ∀ x, ρv (transport x) = ρv x) :
    (frobenioidValueKernelOfValueMap ρv hρv_mul hρv_one transport
      htransport).realification = ρv :=
  rfl

/-- Consumption hook: the real degree of every element is its value. -/
theorem frobenioidValueKernelOfValueMap_degree_coe {X : Type ux} [CommMonoid X]
    (ρv : X → Real) (hρv_mul : ∀ x y, ρv (x * y) = ρv x + ρv y)
    (hρv_one : ρv 1 = 0)
    (transport : X → X) (htransport : ∀ x, ρv (transport x) = ρv x) (x : X) :
    ((frobenioidValueKernelOfValueMap ρv hρv_mul hρv_one transport
      htransport).degree x : Real) = ρv x :=
  rfl

/-! ## 2. From value maps to the K2 Frobenioid construction -/

/-- Two value maps with aligned `modMap`/`MODMap` data form the reduced link
layer consumed by K2.  The degree equations are the alignment equations of the
two value maps, since both degrees are `Multiplicative.ofAdd ∘ ρv` by
construction. -/
def primeStripFrobenioidLinkLayerOfValueMaps
    {X : Type ux} {Y : Type uy} [CommMonoid X] [CommMonoid Y]
    (ρvX : X → Real) (hX_mul : ∀ x y, ρvX (x * y) = ρvX x + ρvX y)
    (hX_one : ρvX 1 = 0)
    (transportX : X → X) (hX_transport : ∀ x, ρvX (transportX x) = ρvX x)
    (ρvY : Y → Real) (hY_mul : ∀ y z, ρvY (y * z) = ρvY y + ρvY z)
    (hY_one : ρvY 1 = 0)
    (transportY : Y → Y) (hY_transport : ∀ y, ρvY (transportY y) = ρvY y)
    (modMap : X → Y) (mod_value : ∀ x, ρvY (modMap x) = ρvX x)
    (mod_transport : ∀ x, modMap (transportX x) = transportY (modMap x))
    (MODMap : Y → X) (MOD_value : ∀ y, ρvX (MODMap y) = ρvY y)
    (MOD_transport : ∀ y, MODMap (transportY y) = transportX (MODMap y)) :
    PrimeStripFrobenioidLinkLayer X Y where
  localFrobenioid :=
    frobenioidValueKernelOfValueMap ρvX hX_mul hX_one transportX hX_transport
  globalFrobenioid :=
    frobenioidValueKernelOfValueMap ρvY hY_mul hY_one transportY hY_transport
  modMap := modMap
  MODMap := MODMap
  mod_degree := fun x => by
    change Multiplicative.ofAdd (ρvY (modMap x)) = Multiplicative.ofAdd (ρvX x)
    exact congrArg Multiplicative.ofAdd (mod_value x)
  MOD_degree := fun y => by
    change Multiplicative.ofAdd (ρvX (MODMap y)) = Multiplicative.ofAdd (ρvY y)
    exact congrArg Multiplicative.ofAdd (MOD_value y)
  mod_transport := mod_transport
  MOD_transport := MOD_transport

/-- Kepler REQ-2 supply, K2 form: value maps with aligned `mod`/`MOD` data reach
the frozen `K2FrobenioidBoundary` through `k2FrobenioidBoundaryOfLinkLayer`.
The value maps are exactly the `localFrobenioid` / `globalFrobenioid`
realifications of the resulting record.  The remaining inputs are unchanged
from item 28 (the K2 boundary record): the source realization `R`, the K1
vertical carrier `K`, and the four comparison alignments. -/
def k2FrobenioidBoundaryOfValueMaps
    (R : SourceTheorem311Realization l Label Choice)
    (K : K1VerticalBoundary R.procession R.packet)
    {X : Type ux} {Y : Type uy} [CommMonoid X] [CommMonoid Y]
    (ρvX : X → Real) (hX_mul : ∀ x y, ρvX (x * y) = ρvX x + ρvX y)
    (hX_one : ρvX 1 = 0)
    (transportX : X → X) (hX_transport : ∀ x, ρvX (transportX x) = ρvX x)
    (ρvY : Y → Real) (hY_mul : ∀ y z, ρvY (y * z) = ρvY y + ρvY z)
    (hY_one : ρvY 1 = 0)
    (transportY : Y → Y) (hY_transport : ∀ y, ρvY (transportY y) = ρvY y)
    (modMap : X → Y) (mod_value : ∀ x, ρvY (modMap x) = ρvX x)
    (mod_transport : ∀ x, modMap (transportX x) = transportY (modMap x))
    (MODMap : Y → X) (MOD_value : ∀ y, ρvX (MODMap y) = ρvY y)
    (MOD_transport : ∀ y, MODMap (transportY y) = transportX (MODMap y))
    (comparison : SourceProposition310Comparison Choice Choice)
    (comparison_local : comparison.localMap =
      R.evaluation.evaluation.localMap)
    (comparison_global : comparison.globalMap =
      R.evaluation.evaluation.globalMap)
    (comparison_lower : comparison.lower =
      R.evaluation.evaluation.localComp)
    (comparison_upper : comparison.upper =
      R.evaluation.evaluation.globalComp) :
    K2FrobenioidBoundary R K X Y :=
  k2FrobenioidBoundaryOfLinkLayer R K
    (primeStripFrobenioidLinkLayerOfValueMaps ρvX hX_mul hX_one transportX
      hX_transport ρvY hY_mul hY_one transportY hY_transport modMap mod_value
      mod_transport MODMap MOD_value MOD_transport)
    comparison comparison_local comparison_global comparison_lower
    comparison_upper

/-! ## 3. Card: the image identifications are additional hypotheses -/

/-- The rational-image predicate: the range statement behind the downstream
identification `v((Q̄p)^×) = ℚ`.  It is *additional input* for a consumer of the
value-map entry: no kernel/link-layer/K2 field constrains the range. -/
def ValueMapRationalImage {X : Type ux} (ρv : X → Real) : Prop :=
  Set.range ρv = Set.range (fun q : ℚ => (q : Real))

/-- The scaled rational-image predicate: the range statement behind the degree
image `ℚ · log p` (at `scale = Real.log p`), or the plain value-range form at
`scale = 1`. -/
def ValueMapScaledRationalImage {X : Type ux} (scale : Real) (ρv : X → Real) :
    Prop :=
  Set.range (fun x => scale * ρv x) =
    Set.range (fun q : ℚ => scale * (q : Real))

/-- The one implication supplied by the entry: a rational image scales to the
`ℚ · log p`-type degree image.  (The converse fails at `scale = 0`; only this
direction is used by the downstream consumption.) -/
theorem valueMapScaledRationalImage_of_rationalImage {X : Type ux} {scale : Real}
    {ρv : X → Real} (h : ValueMapRationalImage ρv) :
    ValueMapScaledRationalImage scale ρv := by
  have h' : Set.range ρv = Set.range (fun q : ℚ => (q : Real)) := h
  unfold ValueMapScaledRationalImage
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    have hx : ρv x ∈ Set.range (fun q : ℚ => (q : Real)) := by
      rw [← h']
      exact ⟨x, rfl⟩
    obtain ⟨q, hq⟩ := hx
    have hq' : (q : Real) = ρv x := hq
    exact ⟨q, congrArg (fun r : Real => scale * r) hq'⟩
  · rintro ⟨q, rfl⟩
    have hq : (q : Real) ∈ Set.range ρv := by
      rw [h']
      exact ⟨q, rfl⟩
    obtain ⟨x, hx⟩ := hq
    have hx' : ρv x = (q : Real) := hx
    exact ⟨x, congrArg (fun r : Real => scale * r) hx'⟩

/-- The constant-zero value map is an admissible kernel datum: the kernel laws
impose no nondegeneracy on a value map. -/
def zeroValueMapKernel (X : Type ux) [CommMonoid X] : FrobenioidValueKernel X :=
  frobenioidValueKernelOfValueMap (fun _ => (0 : Real))
    (by intro x y; simp)
    rfl
    id
    (by intro x; rfl)

/-- Separation witness for the card: an admissible value kernel whose image is
`{0}`, hence not the rational line.  The Frobenioid value-kernel laws therefore
do not imply `v((Q̄p)^×) = ℚ`; that identification must come from the source
arithmetic (or be carried as an explicit hypothesis). -/
theorem zeroValueMapKernel_not_rationalImage (X : Type ux) [CommMonoid X] :
    ¬ ValueMapRationalImage (zeroValueMapKernel X).realification := by
  intro h
  have h' : Set.range (zeroValueMapKernel X).realification =
      Set.range (fun q : ℚ => (q : Real)) := h
  have hmem : (2 : Real) ∈ Set.range (zeroValueMapKernel X).realification := by
    rw [h']
    exact ⟨(2 : ℚ), rfl⟩
  obtain ⟨x, hx⟩ := hmem
  have h0 : (zeroValueMapKernel X).realification x = 0 := rfl
  rw [h0] at hx
  exact absurd hx (by norm_num)

end

end K1K2Realization

end LeanFormal.IUT
