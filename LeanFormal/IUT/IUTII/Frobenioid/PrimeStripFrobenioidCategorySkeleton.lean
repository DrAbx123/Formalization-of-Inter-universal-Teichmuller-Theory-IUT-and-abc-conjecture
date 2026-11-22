import LeanFormal.IUT.IUTII.Frobenioid.PrimeStripFrobenioidCards
import LeanFormal.IUT.IUTI.HodgeTheater.LocalPrimePlaces
import LeanFormal.IUT.IUTIII.Theorem311.Indeterminacy.StepXFormalQuotientVerticalLogKummerDocking
import LeanFormal.IUT.IUTIII.Theorem311.SourceK1K2ValueMapEntry

/-!
# The Frobenioid category layer at the prime strip: functoriality and skeleton laws

Source anchor: Frobenioids I, Definition 1.1, (iii)-(iv) (txt 833-888) and
Definition 1.2 / Remark 1.1.1 (txt 889-920).  In (iii) the elementary
Frobenioid `F_Phi` attached to a monoid `Phi` on a category `D` has the objects
of `D` and the morphisms `phi = (phi_D, Z_phi, n_phi)`, with composite
`psi circ phi = (psi_D circ phi_D, phi_D^*(Z_psi) + n_psi . Z_phi, n_psi . n_phi)`;
the assignment `Phi |-> F_Phi` is "functorial with respect to homomorphisms of
functors `Phi -> Phi'`", and the natural projection `F_Phi -> D` is part of the
data.  These are the structures formalized in `Iut/Foundations/Frobenioid.lean`
(`Iut.ElementaryFrobenioid`, `Iut.ElementaryFrobenioidHom`); the present file
supplies the missing functoriality in `Phi` and the categorical laws on the
frozen link-layer contract.

Contents:

* `DivisorialMonoidOnHom` with its identity, composition and application laws:
  the homomorphisms of functors `Phi -> Psi` of Definition 1.1, (iii).
* `elementaryFrobenioidHomMap` and `elementaryFrobenioidMapFunctor`: the map on
  morphisms `F_Phi -> F_Psi` and the induced Mathlib functor, with `map_id` and
  `map_comp` discharged from the composite formula; the `id`/`comp` laws at the
  functor level, compatibility with the natural projection `F_Phi -> D`, and
  faithfulness on pointwise injective object mappings.
* Link-layer skeleton laws on the frozen `PrimeStripFrobenioidLinkLayer`
  contract of `PrimeStripsFrobenioidLinks.lean`: identity, composition over a
  shared intermediate kernel, the induced projection equations, and uniqueness
  of the compatible `modMap`/`MODMap` over degree-injective kernels.
* Boundary (4) minimal layer: the `N >= 1` power dynamics on a commutative
  monoid (`valueFrobeniusPower`), with its unit/multiplication laws and the
  degree law `realification (x^n) = n * realification x`.
* Boundary (1) evaluation, proved: the geometric kernel of the concrete local
  D-prime-strips of `LocalPrimePlaces.lean` is trivial at every place
  (`localDPrimeStrip_geometric_eq_bot`, `finiteLocalDPrimeStrip_geometric_eq_bot`),
  while the source demands the geometric fundamental group as kernel
  (`geometricPiOneBoundary`, `PlaceCompletionCarrier.lean:287`).

Boundary cards kept (details in the audit note at the end of the file):

* (1) etale pi_1: object = the geometric fundamental group of a smooth proper
  geometrically connected curve over a number field, with the functorial
  surjection onto the local absolute Galois group and the exact sequence
  `1 -> pi_1^geo -> pi_1^et(X) -> Gal(Kbar/K) -> 1` (IUT II, Sections 3-6;
  consumers `VerticalLogKummer`, K1/K2).  Not constructed; Mathlib has no etale
  fundamental group of a curve, and the kernel is arithmetic content.
* (2) V_K transport and the rho_v normalization: object = the place completions
  `K_v` of the base field `K = Fmod` with the transport over `V_K` and the
  isomorphism `rho_v : Phi(C|mod),v ~= Phi^rlf(C|-v)` normalizing `log|-mod(pv)`
  to `1/[Kv:(Fmod)v] * logPhi(pv)` (IUT I, Example 3.5, (i), txt 4569ff;
  consumers `SourceOriginalInput`, K2).  The completion carrier exists
  (`numberFieldPlaceCompletionCarrier`), but the prime-strip-layer transport is
  absent; the tree has only `K = Q` carriers.
* (4) Frobenius data: object = the Frobenius dynamics on the value/divisor
  monoids with the log-shell compatibility ([FrdI] Definitions 1.2/1.3;
  consumers `VerticalLogKummerCorrespondence.upperSemi`, `Ind3`).  The value
  side is carried by this file's `valueFrobeniusPower`; the divisor side is
  blocked by the missing sharp divisorial monoid (see
  `PrimeStripFrobenioidSkeletonCards.lean:137`).

The deep structure (structure equivalence and restrictions of Frobenioids,
[FrdI] Corollary 4.11) is out of scope for this round.
-/

noncomputable section

namespace LeanFormal.IUT

open CategoryTheory

universe u ux uy uz uw

/-! ## 1. Homomorphisms of divisorial monoids on a category -/

/-- A homomorphism of divisorial monoids `Phi -> Psi` on `D` in the sense of
Frobenioids I, Definition 1.1, (iii) ("functorial with respect to homomorphisms
of functors"): objectwise a homomorphism of additive monoids commuting with all
pullbacks. -/
structure DivisorialMonoidOnHom
    {D : Type u} [Category.{u} D]
    {IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop}
    {IsFSM' : ∀ {X Y : D}, (X ⟶ Y) → Prop}
    (Phi : Iut.DivisorialMonoidOn D IsFSM) (Psi : Iut.DivisorialMonoidOn D IsFSM') where
  hom : ∀ X, (Phi.obj X).carrier →+ (Psi.obj X).carrier
  naturality : ∀ {X Y : D} (f : X ⟶ Y) (x : (Phi.obj Y).carrier),
    hom X (Phi.pullback f x) = Psi.pullback f (hom Y x)

namespace DivisorialMonoidOnHom

variable {D : Type u} [Category.{u} D]
variable {IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop}
variable {IsFSM' : ∀ {X Y : D}, (X ⟶ Y) → Prop}
variable {IsFSM'' : ∀ {X Y : D}, (X ⟶ Y) → Prop}
variable {Phi : Iut.DivisorialMonoidOn D IsFSM}
variable {Psi : Iut.DivisorialMonoidOn D IsFSM'}
variable {Chi : Iut.DivisorialMonoidOn D IsFSM''}

/-- The identity homomorphism of divisorial monoids. -/
protected def id : DivisorialMonoidOnHom Phi Phi where
  hom X := AddMonoidHom.id (Phi.obj X).carrier
  naturality := fun _ _ => rfl

/-- Composition of homomorphisms of divisorial monoids. -/
def comp (eta : DivisorialMonoidOnHom Phi Psi) (xi : DivisorialMonoidOnHom Psi Chi) :
    DivisorialMonoidOnHom Phi Chi where
  hom X := (xi.hom X).comp (eta.hom X)
  naturality := fun f x => by
    simp only [AddMonoidHom.comp_apply]
    rw [eta.naturality f x, xi.naturality f (eta.hom _ x)]

@[simp] theorem id_apply (X : D) (x : (Phi.obj X).carrier) :
      (DivisorialMonoidOnHom.id : DivisorialMonoidOnHom Phi Phi).hom X x = x := rfl

@[simp] theorem comp_apply (eta : DivisorialMonoidOnHom Phi Psi)
    (xi : DivisorialMonoidOnHom Psi Chi) (X : D) (x : (Phi.obj X).carrier) :
    (eta.comp xi).hom X x = xi.hom X (eta.hom X x) := rfl

end DivisorialMonoidOnHom

/-! ## 2. The induced map on morphisms and the functor of elementary Frobenioids -/

/-- The map on morphisms of the elementary Frobenioids induced by a
homomorphism `eta : Phi -> Psi` of monoids on `D`: the base morphism and the
Frobenius degree are preserved, and the zero divisor is pushed along `eta`. -/
def elementaryFrobenioidHomMap {D : Type u} [Category.{u} D]
    {IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop}
    {IsFSM' : ∀ {X Y : D}, (X ⟶ Y) → Prop}
    {Phi : Iut.DivisorialMonoidOn D IsFSM} {Psi : Iut.DivisorialMonoidOn D IsFSM'}
    (eta : DivisorialMonoidOnHom Phi Psi)
    {X Y : D} (f : Iut.ElementaryFrobenioidHom Phi X Y) :
    Iut.ElementaryFrobenioidHom Psi X Y where
  base := f.base
  divisor := eta.hom X f.divisor
  frobeniusDegree := f.frobeniusDegree

@[simp] theorem elementaryFrobenioidHomMap_base {D : Type u} [Category.{u} D]
    {IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop}
    {IsFSM' : ∀ {X Y : D}, (X ⟶ Y) → Prop}
    {Phi : Iut.DivisorialMonoidOn D IsFSM} {Psi : Iut.DivisorialMonoidOn D IsFSM'}
    (eta : DivisorialMonoidOnHom Phi Psi)
    {X Y : D} (f : Iut.ElementaryFrobenioidHom Phi X Y) :
    (elementaryFrobenioidHomMap eta f).base = f.base := rfl

@[simp] theorem elementaryFrobenioidHomMap_divisor {D : Type u} [Category.{u} D]
    {IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop}
    {IsFSM' : ∀ {X Y : D}, (X ⟶ Y) → Prop}
    {Phi : Iut.DivisorialMonoidOn D IsFSM} {Psi : Iut.DivisorialMonoidOn D IsFSM'}
    (eta : DivisorialMonoidOnHom Phi Psi)
    {X Y : D} (f : Iut.ElementaryFrobenioidHom Phi X Y) :
    (elementaryFrobenioidHomMap eta f).divisor = eta.hom X f.divisor := rfl

@[simp] theorem elementaryFrobenioidHomMap_degree {D : Type u} [Category.{u} D]
    {IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop}
    {IsFSM' : ∀ {X Y : D}, (X ⟶ Y) → Prop}
    {Phi : Iut.DivisorialMonoidOn D IsFSM} {Psi : Iut.DivisorialMonoidOn D IsFSM'}
    (eta : DivisorialMonoidOnHom Phi Psi)
    {X Y : D} (f : Iut.ElementaryFrobenioidHom Phi X Y) :
    (elementaryFrobenioidHomMap eta f).frobeniusDegree = f.frobeniusDegree := rfl
/-- Functoriality of `Phi |-> F_Phi` (Frobenioids I, Definition 1.1, (iii),
txt 853-854): a homomorphism of functors `Phi -> Psi` induces a functor
between the elementary Frobenioids, preserving objects, base morphisms and
Frobenius degrees, and pushing zero divisors along `eta`. -/
def elementaryFrobenioidMapFunctor {D : Type u} [Category.{u} D]
    {IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop}
    {IsFSM' : ∀ {X Y : D}, (X ⟶ Y) → Prop}
    {Phi : Iut.DivisorialMonoidOn D IsFSM} {Psi : Iut.DivisorialMonoidOn D IsFSM'}
    (eta : DivisorialMonoidOnHom Phi Psi) :
    Iut.ElementaryFrobenioid D IsFSM Phi ⥤ Iut.ElementaryFrobenioid D IsFSM' Psi where
  obj X := X
  map f := elementaryFrobenioidHomMap eta f
  map_id X := by
    change elementaryFrobenioidHomMap eta (Iut.ElementaryFrobenioidHom.id Phi X) =
      Iut.ElementaryFrobenioidHom.id Psi X
    ext <;> simp [elementaryFrobenioidHomMap, Iut.ElementaryFrobenioidHom.id]
  map_comp f g := by
    change elementaryFrobenioidHomMap eta (Iut.ElementaryFrobenioidHom.comp Phi f g) =
      Iut.ElementaryFrobenioidHom.comp Psi
        (elementaryFrobenioidHomMap eta f) (elementaryFrobenioidHomMap eta g)
    ext
    · simp
    · simp only [elementaryFrobenioidHomMap,
        Iut.ElementaryFrobenioidHom.comp_divisor]
      rw [map_add, map_nsmul, eta.naturality f.base g.divisor]
    · simp

@[simp] theorem elementaryFrobenioidMapFunctor_id_hom {D : Type u} [Category.{u} D]
    {IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop}
    {Phi : Iut.DivisorialMonoidOn D IsFSM}
    {X Y : D} (f : Iut.ElementaryFrobenioidHom Phi X Y) :
    (elementaryFrobenioidMapFunctor
        (DivisorialMonoidOnHom.id : DivisorialMonoidOnHom Phi Phi)).map f = f := rfl

@[simp] theorem elementaryFrobenioidMapFunctor_comp_hom {D : Type u} [Category.{u} D]
    {IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop}
    {IsFSM' : ∀ {X Y : D}, (X ⟶ Y) → Prop}
    {IsFSM'' : ∀ {X Y : D}, (X ⟶ Y) → Prop}
    {Phi : Iut.DivisorialMonoidOn D IsFSM} {Psi : Iut.DivisorialMonoidOn D IsFSM'}
    {Chi : Iut.DivisorialMonoidOn D IsFSM''}
    (eta : DivisorialMonoidOnHom Phi Psi) (xi : DivisorialMonoidOnHom Psi Chi)
    {X Y : D} (f : Iut.ElementaryFrobenioidHom Phi X Y) :
    (elementaryFrobenioidMapFunctor (eta.comp xi)).map f =
      (elementaryFrobenioidMapFunctor xi).map
        ((elementaryFrobenioidMapFunctor eta).map f) := rfl

/-- The induced functors commute with the natural projections to the base
category `D` (Frobenioids I, Definition 1.1, (iii), txt 855-856): the triangle
`F_Phi -> F_Psi -> D` equals `F_Phi -> D`. -/
theorem elementaryFrobenioidMapFunctor_comp_base {D : Type u} [Category.{u} D]
    {IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop}
    {IsFSM' : ∀ {X Y : D}, (X ⟶ Y) → Prop}
    {Phi : Iut.DivisorialMonoidOn D IsFSM} {Psi : Iut.DivisorialMonoidOn D IsFSM'}
    (eta : DivisorialMonoidOnHom Phi Psi) :
    (elementaryFrobenioidMapFunctor eta) ⋙ Iut.ElementaryFrobenioid.base Psi =
      Iut.ElementaryFrobenioid.base Phi := by
  rfl

/-- The functor induced by the identity homomorphism is the identity functor. -/
theorem elementaryFrobenioidMapFunctor_id {D : Type u} [Category.{u} D]
    {IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop}
    {Phi : Iut.DivisorialMonoidOn D IsFSM} :
    (elementaryFrobenioidMapFunctor
        (DivisorialMonoidOnHom.id : DivisorialMonoidOnHom Phi Phi)) =
      𝟭 (Iut.ElementaryFrobenioid D IsFSM Phi) := by
  rfl

/-- Faithfulness of the functoriality in `Phi` on degree-injective object
mappings: if every `eta.hom X` is injective, then the induced map on morphisms
is injective, so distinct morphisms of `F_Phi` stay distinct in `F_Psi`. -/
theorem elementaryFrobenioidHomMap_injective_of_hom_injective
    {D : Type u} [Category.{u} D]
    {IsFSM : ∀ {X Y : D}, (X ⟶ Y) → Prop}
    {IsFSM' : ∀ {X Y : D}, (X ⟶ Y) → Prop}
    {Phi : Iut.DivisorialMonoidOn D IsFSM} {Psi : Iut.DivisorialMonoidOn D IsFSM'}
    (eta : DivisorialMonoidOnHom Phi Psi)
    (hinj : ∀ X, Function.Injective (eta.hom X)) (X Y : D) :
    Function.Injective
      (elementaryFrobenioidHomMap (X := X) (Y := Y) eta) := by
  intro f g hfg
  apply Iut.ElementaryFrobenioidHom.ext
  · exact congrArg (fun h : Iut.ElementaryFrobenioidHom Psi X Y => h.base) hfg
  · exact hinj X (congrArg Iut.ElementaryFrobenioidHom.divisor hfg)
  · exact congrArg (fun h : Iut.ElementaryFrobenioidHom Psi X Y => h.frobeniusDegree) hfg

/-! ## 3. Skeleton laws of the frozen link-layer contract -/

namespace PrimeStripFrobenioidLinkLayer

variable {X : Type ux} {Y : Type uy} {Z : Type uz} {W : Type uw}
variable [CommMonoid X] [CommMonoid Y] [CommMonoid Z] [CommMonoid W]

/-- The identity link layer at a kernel: the identity tuple of
Frobenioids I, Definition 1.1, (iii) (`Z = 0`, `n = 1`, identity base). -/
def id (k : FrobenioidValueKernel X) : PrimeStripFrobenioidLinkLayer X X where
  localFrobenioid := k
  globalFrobenioid := k
  modMap := fun x => x
  MODMap := fun y => y
  mod_degree := fun _ => rfl
  MOD_degree := fun _ => rfl
  mod_transport := fun _ => rfl
  MOD_transport := fun _ => rfl

/-- Composition of link layers over a shared intermediate kernel: compose the
two `mod` maps and the two `MOD` maps in the opposite order, and keep the outer
kernels.  The shared-kernel hypothesis is an equality of the two kernels at
the intermediate carrier. -/
def comp (L₁ : PrimeStripFrobenioidLinkLayer X Y)
    (L₂ : PrimeStripFrobenioidLinkLayer Y Z)
    (hshare : L₁.globalFrobenioid = L₂.localFrobenioid) :
    PrimeStripFrobenioidLinkLayer X Z where
  localFrobenioid := L₁.localFrobenioid
  globalFrobenioid := L₂.globalFrobenioid
  modMap := fun x => L₂.modMap (L₁.modMap x)
  MODMap := fun z => L₁.MODMap (L₂.MODMap z)
  mod_degree := fun x => by
    rw [L₂.mod_degree (L₁.modMap x), ← hshare, L₁.mod_degree]
  MOD_degree := fun z => by
    rw [L₁.MOD_degree (L₂.MODMap z), hshare, L₂.MOD_degree]
  mod_transport := fun x => by
    rw [L₁.mod_transport x]
    have htr : L₁.globalFrobenioid.transport = L₂.localFrobenioid.transport :=
      congrArg FrobenioidValueKernel.transport hshare
    rw [htr]
    exact L₂.mod_transport (L₁.modMap x)
  MOD_transport := fun z => by
    rw [L₂.MOD_transport z]
    have htr : L₁.globalFrobenioid.transport = L₂.localFrobenioid.transport :=
      congrArg FrobenioidValueKernel.transport hshare
    rw [← htr]
    exact L₁.MOD_transport (L₂.MODMap z)

@[simp] theorem id_localFrobenioid (k : FrobenioidValueKernel X) :
    (id k).localFrobenioid = k := rfl

@[simp] theorem id_globalFrobenioid (k : FrobenioidValueKernel X) :
    (id k).globalFrobenioid = k := rfl

@[simp] theorem id_modMap (k : FrobenioidValueKernel X) :
    (id k).modMap = fun x => x := rfl

@[simp] theorem id_MODMap (k : FrobenioidValueKernel X) :
    (id k).MODMap = fun y => y := rfl

@[simp] theorem comp_localFrobenioid (L₁ : PrimeStripFrobenioidLinkLayer X Y)
    (L₂ : PrimeStripFrobenioidLinkLayer Y Z)
    (hshare : L₁.globalFrobenioid = L₂.localFrobenioid) :
    (L₁.comp L₂ hshare).localFrobenioid = L₁.localFrobenioid := rfl

@[simp] theorem comp_globalFrobenioid (L₁ : PrimeStripFrobenioidLinkLayer X Y)
    (L₂ : PrimeStripFrobenioidLinkLayer Y Z)
    (hshare : L₁.globalFrobenioid = L₂.localFrobenioid) :
    (L₁.comp L₂ hshare).globalFrobenioid = L₂.globalFrobenioid := rfl

@[simp] theorem comp_modMap (L₁ : PrimeStripFrobenioidLinkLayer X Y)
    (L₂ : PrimeStripFrobenioidLinkLayer Y Z)
    (hshare : L₁.globalFrobenioid = L₂.localFrobenioid) :
    (L₁.comp L₂ hshare).modMap = fun x => L₂.modMap (L₁.modMap x) := rfl

@[simp] theorem comp_MODMap (L₁ : PrimeStripFrobenioidLinkLayer X Y)
    (L₂ : PrimeStripFrobenioidLinkLayer Y Z)
    (hshare : L₁.globalFrobenioid = L₂.localFrobenioid) :
    (L₁.comp L₂ hshare).MODMap = fun z => L₁.MODMap (L₂.MODMap z) := rfl

/-- Left identity law of the layer composition: composing the identity layer
(at the local kernel) with `L` over the canonical shared-kernel proof gives
back `L`.  The two components compute as `id o modMap = modMap` and
`MODMap o id = MODMap`. -/
theorem id_comp (L : PrimeStripFrobenioidLinkLayer X Y)
    (h : (id L.localFrobenioid).globalFrobenioid = L.localFrobenioid) :
    (id L.localFrobenioid).comp L h = L := by
  rcases L with ⟨lf, gf, mm, MM, dM, dD, tM, tD⟩
  rfl

/-- Right identity law of the layer composition. -/
theorem comp_id (L : PrimeStripFrobenioidLinkLayer X Y)
    (h : L.globalFrobenioid = (id L.globalFrobenioid).localFrobenioid) :
    L.comp (id L.globalFrobenioid) h = L := by
  rcases L with ⟨lf, gf, mm, MM, dM, dD, tM, tD⟩
  rfl

/-- Associativity of the layer composition over nested shared kernels. -/
theorem comp_assoc (L₁ : PrimeStripFrobenioidLinkLayer X Y)
    (L₂ : PrimeStripFrobenioidLinkLayer Y Z)
    (L₃ : PrimeStripFrobenioidLinkLayer Z W)
    (h₁₂ : L₁.globalFrobenioid = L₂.localFrobenioid)
    (h₂₃ : L₂.globalFrobenioid = L₃.localFrobenioid) :
    (L₁.comp L₂ h₁₂).comp L₃ h₂₃ =
      L₁.comp (L₂.comp L₃ h₂₃) h₁₂ := by
  rcases L₁ with ⟨lf₁, gf₁, mm₁, MM₁, d₁, D₁, t₁, T₁⟩
  rcases L₂ with ⟨lf₂, gf₂, mm₂, MM₂, d₂, D₂, t₂, T₂⟩
  rcases L₃ with ⟨lf₃, gf₃, mm₃, MM₃, d₃, D₃, t₃, T₃⟩
  rfl

/-- Extensionality of the link-layer contract on its four data fields: two
layers with equal kernels and equal maps are equal (the compatibility proofs
are propositions). -/
theorem linkLayer_ext (L₁ L₂ : PrimeStripFrobenioidLinkLayer X Y)
    (hl : L₁.localFrobenioid = L₂.localFrobenioid)
    (hg : L₁.globalFrobenioid = L₂.globalFrobenioid)
    (hm : L₁.modMap = L₂.modMap) (hM : L₁.MODMap = L₂.MODMap) :
    L₁ = L₂ := by
  rcases L₁ with ⟨lf₁, gf₁, mm₁, MM₁, d₁, D₁, t₁, T₁⟩
  rcases L₂ with ⟨lf₂, gf₂, mm₂, MM₂, d₂, D₂, t₂, T₂⟩
  subst hl
  subst hg
  subst hm
  subst hM
  rfl

/-- Uniqueness of the compatible `mod` map over a degree-injective global
kernel: any two maps satisfying the degree equation of `ModDirectionCard`
coincide. -/
theorem modMap_unique_of_degree_injective
    {localKernel : FrobenioidValueKernel X} {globalKernel : FrobenioidValueKernel Y}
    (hinj : Function.Injective globalKernel.degree)
    {m₁ m₂ : X → Y}
    (h₁ : ∀ x, globalKernel.degree (m₁ x) = localKernel.degree x)
    (h₂ : ∀ x, globalKernel.degree (m₂ x) = localKernel.degree x) :
    m₁ = m₂ :=
  funext fun x => hinj ((h₁ x).trans (h₂ x).symm)

/-- Uniqueness of the compatible `MOD` map over a degree-injective local
kernel, the `MOD`-side counterpart of `modMap_unique_of_degree_injective`. -/
theorem MODMap_unique_of_degree_injective
    {localKernel : FrobenioidValueKernel X} {globalKernel : FrobenioidValueKernel Y}
    (hinj : Function.Injective localKernel.degree)
    {m₁ m₂ : Y → X}
    (h₁ : ∀ y, localKernel.degree (m₁ y) = globalKernel.degree y)
    (h₂ : ∀ y, localKernel.degree (m₂ y) = globalKernel.degree y) :
    m₁ = m₂ :=
  funext fun y => hinj ((h₁ y).trans (h₂ y).symm)

/-- Uniqueness of the link layer over degree-injective kernels sharing the
same data: two layers with the same kernels are equal, because both maps are
determined by their degree equations. -/
theorem linkLayer_eq_of_degree_injective
    (L₁ L₂ : PrimeStripFrobenioidLinkLayer X Y)
    (hinjL : Function.Injective L₁.localFrobenioid.degree)
    (hinjG : Function.Injective L₁.globalFrobenioid.degree)
    (hl : L₁.localFrobenioid = L₂.localFrobenioid)
    (hg : L₁.globalFrobenioid = L₂.globalFrobenioid) :
    L₁ = L₂ := by
  refine linkLayer_ext L₁ L₂ hl hg ?_ ?_
  · funext x
    apply hinjG
    calc L₁.globalFrobenioid.degree (L₁.modMap x)
        = L₁.localFrobenioid.degree x := L₁.mod_degree x
      _ = L₂.localFrobenioid.degree x :=
          DFunLike.congr_fun (congrArg FrobenioidValueKernel.degree hl) x
      _ = L₂.globalFrobenioid.degree (L₂.modMap x) := (L₂.mod_degree x).symm
      _ = L₁.globalFrobenioid.degree (L₂.modMap x) :=
          DFunLike.congr_fun (congrArg FrobenioidValueKernel.degree hg.symm) _
  · funext y
    apply hinjL
    calc L₁.localFrobenioid.degree (L₁.MODMap y)
        = L₁.globalFrobenioid.degree y := L₁.MOD_degree y
      _ = L₂.globalFrobenioid.degree y :=
          DFunLike.congr_fun (congrArg FrobenioidValueKernel.degree hg) y
      _ = L₂.localFrobenioid.degree (L₂.MODMap y) := (L₂.MOD_degree y).symm
      _ = L₁.localFrobenioid.degree (L₂.MODMap y) :=
          DFunLike.congr_fun (congrArg FrobenioidValueKernel.degree hl.symm) _

end PrimeStripFrobenioidLinkLayer

/-! ## 4. Boundary (4) minimal layer: the power dynamics on values -/

/-- The `N >= 1` power dynamics of Frobenioids I, Definition 1.1, (iii) on the
value side: on a commutative monoid the Frobenius degree `n` acts by
`x |-> x^n`, a monoid endomorphism.  This is the value-side fragment of the
Frobenius data of boundary item (4); the divisor side and the log-shell
compatibility are not carried by the current group-valued prime-strip
carriers (see the audit note). -/
noncomputable def valueFrobeniusPower {X : Type ux} [CommMonoid X] (n : ℕ+) :
    X →* X where
  toFun x := x ^ (n : ℕ)
  map_one' := one_pow _
  map_mul' x y := mul_pow x y _

@[simp] theorem valueFrobeniusPower_apply {X : Type ux} [CommMonoid X]
    (n : ℕ+) (x : X) :
    valueFrobeniusPower n x = x ^ (n : ℕ) := rfl

/-- The dynamics send `1` to the identity endomorphism. -/
theorem valueFrobeniusPower_one {X : Type ux} [CommMonoid X] :
    valueFrobeniusPower (1 : ℕ+) = MonoidHom.id X := by
  ext x
  simp [valueFrobeniusPower]

/-- The dynamics are multiplicative in the Frobenius degree:
`x |-> x^(m*n)` is `x |-> (x^m)^n`. -/
theorem valueFrobeniusPower_mul {X : Type ux} [CommMonoid X] (m n : ℕ+) :
    valueFrobeniusPower (X := X) (m * n) =
      (valueFrobeniusPower (X := X) n).comp (valueFrobeniusPower (X := X) m) := by
  ext x
  simp only [MonoidHom.comp_apply, valueFrobeniusPower_apply]
  rw [← pow_mul, PNat.mul_coe]

/-- Degree law of the power dynamics at a Frobenioid value kernel: the
Multiplicative-real degree of `x^n` is the `n`-th power of the degree of `x`,
i.e. `n` times it on the additive side (the degree multiplication of the
Frobenius degree in Definition 1.1, (iii)). -/
theorem valueFrobeniusPower_degree {X : Type ux} [CommMonoid X]
    (K : FrobenioidValueKernel X) (n : ℕ+) (x : X) :
    K.degree (valueFrobeniusPower n x) = (K.degree x) ^ (n : ℕ) :=
  map_pow K.degree x (n : ℕ)

/-- Additive form of `valueFrobeniusPower_degree`: the realified degree of
`x^n` is `n` times the realified degree of `x`. -/
theorem valueFrobeniusPower_realification {X : Type ux} [CommMonoid X]
    (K : FrobenioidValueKernel X) (x : X) (n : ℕ) :
    K.realification (x ^ n) = (n : ℝ) * K.realification x := by
  induction n with
  | zero =>
      rw [pow_zero, K.unit_realification]
      simp
  | succ n ih =>
      rw [pow_succ, K.realification_mul, ih]
      push_cast
      ring

/-! ## 5. Boundary (1): the geometric kernel of the concrete local strips -/

/-- Boundary (1), evaluated and proved on the current concrete model: the
`proj` of the local D-prime-strip of `LocalPrimePlaces.lean` is the identity
(`LocalPrimePlaces.lean:58`), hence its geometric kernel is trivial at every
place.  The source requires this kernel to be the geometric fundamental group
of the base curve (IUT II, Sections 3-6; `geometricPiOneBoundary`,
`PlaceCompletionCarrier.lean:287`), so the current model does not realize the
boundary item; the gap is recorded as a card. -/
theorem localDPrimeStrip_geometric_eq_bot (v : RationalPrimePlace) :
    localDPrimeStrip.geometric v = ⊥ := by
  change (MonoidHom.id (localDPrimeStrip.Pi v)).ker = ⊥
  ext x
  simp

/-- The finite-prime-strip analogue of `localDPrimeStrip_geometric_eq_bot`
(`LocalPrimePlaces.lean:75`, same identity projection). -/
theorem finiteLocalDPrimeStrip_geometric_eq_bot {lower upper : Nat}
    (v : FinitePrimePlace lower upper) :
    (finiteLocalDPrimeStrip lower upper).geometric v = ⊥ := by
  change (MonoidHom.id ((finiteLocalDPrimeStrip lower upper).Pi v)).ker = ⊥
  ext x
  simp

/-! ## 5. REQ-3 consumer-side docking: the vertical log-Kummer supply

The supply promised by `REQ-3` (Frobenius / log-shell compatibility for the
`VerticalLogKummerCorrespondence` consumer) has been delivered for the
constructed core by `StepXFormalQuotientVerticalLogKummerDocking.lean`
(`StepXFormalQuotient.verticalLogKummerOfConstructedCore`): the constructed
core inhabits the source-facing `VerticalLogKummerCorrespondence` contract
with the stage-one (Ind3) lift as transport, and its `upperSemi` field is
proved from the level-translation law.  The two theorems below are this
file's consumer point for that supply (boundary (4) / REQ-3 row).  The
*source-level* Frobenius carrier for the Frobenioid / log-shell layers is
not built by the docking and remains the exact card recorded here and in
the audit note. -/

/-- REQ-3 consumption: the upper-semi inclusion of the docking's constructed
core at every layer and every procession state (supplier:
`StepXFormalQuotient.verticalLogKummerOfConstructedCore`). -/
theorem stepXFormalQuotientVerticalLogKummer_upperSemi (l : PrimeGeFive)
    (m : Nat) (x : (StepXFormalQuotient.verticalLogKummerOfConstructedCore l).F m) :
    (StepXFormalQuotient.verticalLogKummerOfConstructedCore l).kummer m x ≤
      (StepXFormalQuotient.verticalLogKummerOfConstructedCore l).kummer (m + 1)
        ((StepXFormalQuotient.verticalLogKummerOfConstructedCore l).log m x) :=
  (StepXFormalQuotient.verticalLogKummerOfConstructedCore l).upperSemi m x

/-- REQ-3 consumption, iterated form: the Kummer image is monotone along
the docking's layer transport (the contract's iteration
`kummer_le_transport` applied to the docking instance). -/
theorem stepXFormalQuotientVerticalLogKummer_kummer_le_transport
    (l : PrimeGeFive) (m n : Nat)
    (x : (StepXFormalQuotient.verticalLogKummerOfConstructedCore l).F m) :
    (StepXFormalQuotient.verticalLogKummerOfConstructedCore l).kummer m x ≤
      (StepXFormalQuotient.verticalLogKummerOfConstructedCore l).kummer (m + n)
        ((StepXFormalQuotient.verticalLogKummerOfConstructedCore l).transport m n x) :=
  (StepXFormalQuotient.verticalLogKummerOfConstructedCore l).kummer_le_transport m x n
/-! ## 6. REQ-2 consumer-side docking: the V_K / rho_v value-map entry

The supply promised by `REQ-2` has been delivered by
`SourceK1K2ValueMapEntry.lean` (run `k1k2-realization-20261016`, fourth leaf):
value maps `rho_v : X → Real` with a compatible transport determine the
reduced Frobenioid value kernel (`frobenioidValueKernelOfValueMap`, degree
forced to `Multiplicative.ofAdd` composed with `rho_v`), two aligned value
maps form the link layer (`primeStripFrobenioidLinkLayerOfValueMaps`), and
the value maps reach the frozen `K2FrobenioidBoundary`
(`k2FrobenioidBoundaryOfValueMaps`).  The theorems below are this file's
consumer point for that supply (boundary (2) / boundary (4) rows).

Image-segment status (kept as an exact card, per the supply): the
identifications `v((Qp)^x) = Q` and the degree image `Q * log p` are range
statements on the value map; no kernel / link-layer / K2 field constrains
the range (`zeroValueMapKernel_not_rationalImage`), so they remain
*additional hypotheses* of the consumer, and the only supplied implication
is rational image => scaled rational image
(`valueMapScaledRationalImage_of_rationalImage`).  The source Frobenius
carrier for the Frobenioid / log-shell layers is not built by the supply
either and remains the exact card recorded in the audit note. -/

/-- REQ-2 consumption, value side: the supply's value map is the
realification of the induced Frobenioid value kernel, so the boundary (4)
power dynamics of this file compute the realified degree of `x^n` as `n`
times the value of `x` (supplier:
`K1K2Realization.frobenioidValueKernelOfValueMap`). -/
theorem frobenioidValueKernelOfValueMap_pow_realification {X : Type ux}
    [CommMonoid X] (ρv : X → ℝ)
    (hρv_mul : ∀ x y, ρv (x * y) = ρv x + ρv y)
    (hρv_one : ρv 1 = 0)
    (transport : X → X)
    (htransport : ∀ x, ρv (transport x) = ρv x)
    (x : X) (n : Nat) :
    (K1K2Realization.frobenioidValueKernelOfValueMap ρv hρv_mul
      hρv_one transport htransport).realification (x ^ n) =
      (n : ℝ) * ρv x := by
  have hreal : (K1K2Realization.frobenioidValueKernelOfValueMap ρv
      hρv_mul hρv_one transport htransport).realification = ρv :=
    rfl
  rw [hreal]
  exact valueFrobeniusPower_realification
    (K1K2Realization.frobenioidValueKernelOfValueMap ρv hρv_mul
      hρv_one transport htransport) x n

/-- REQ-2 consumption, link side: in the link layer built from two aligned
value maps, the local degree is forced to `Multiplicative.ofAdd` composed
with the value map (supplier:
`K1K2Realization.primeStripFrobenioidLinkLayerOfValueMaps`). -/
theorem primeStripFrobenioidLinkLayerOfValueMaps_localFrobenioid_degree
    {X : Type ux} {Y : Type uy} [CommMonoid X] [CommMonoid Y]
    (ρvX : X → ℝ)
    (hX_mul : ∀ x y, ρvX (x * y) = ρvX x + ρvX y)
    (hX_one : ρvX 1 = 0)
    (transportX : X → X)
    (hX_transport : ∀ x, ρvX (transportX x) = ρvX x)
    (ρvY : Y → ℝ)
    (hY_mul : ∀ y z, ρvY (y * z) = ρvY y + ρvY z)
    (hY_one : ρvY 1 = 0)
    (transportY : Y → Y)
    (hY_transport : ∀ y, ρvY (transportY y) = ρvY y)
    (modMap : X → Y)
    (mod_value : ∀ x, ρvY (modMap x) = ρvX x)
    (mod_transport : ∀ x, modMap (transportX x) = transportY (modMap x))
    (MODMap : Y → X)
    (MOD_value : ∀ y, ρvX (MODMap y) = ρvY y)
    (MOD_transport : ∀ y,
      MODMap (transportY y) = transportX (MODMap y))
    (x : X) :
    (K1K2Realization.primeStripFrobenioidLinkLayerOfValueMaps ρvX hX_mul
      hX_one transportX hX_transport ρvY hY_mul hY_one transportY
      hY_transport modMap mod_value mod_transport MODMap MOD_value
      MOD_transport).localFrobenioid.degree x =
      Multiplicative.ofAdd (ρvX x) := rfl

end LeanFormal.IUT

end

namespace LeanFormal.IUT.Audit

/-- CAT-R categorical-layer round for `IUT-I-II.prime-strips-frobenioids`,
on top of `IUT-II.prime-strips-frobenioid-link-layer` and
`IUT-II.prime-strips-frobenioid-skeleton-cards`. -/
def primeStripFrobenioidCategorySkeleton : Obligation :=
  { id := "IUT-II.prime-strips-frobenioid-category-skeleton"
    source :=
      "Frobenioids I, Definition 1.1, (iii)-(iv) and Definition 1.2 / " ++
        "Remark 1.1.1 (txt 833-888, 889-920); IUT I, Example 3.5, (i); " ++
        "IUT II, Sections 3-6 (boundary items)"
    status := VerificationStatus.interface
    note :=
      "CAT-R categorical layer. PROVED: functoriality of Phi |-> F_Phi in Phi " ++
        "([FrdI] Def 1.1(iii), txt 853-854) via `DivisorialMonoidOnHom` and " ++
        "`elementaryFrobenioidMapFunctor` (a Mathlib `Functor`, `map_id`/`map_comp` " ++
        "discharged from the composite formula), its id/comp laws, compatibility with " ++
        "the natural projection `F_Phi -> D` (txt 855-856), and faithfulness on " ++
        "pointwise injective object maps. Skeleton laws of the frozen link-layer " ++
        "contract: `PrimeStripFrobenioidLinkLayer.id`, `.comp` over a shared " ++
        "intermediate kernel, the projection / identity / associativity equations, " ++
        "extensionality, and uniqueness of the compatible `modMap`/`MODMap` and of the " ++
        "whole layer over degree-injective kernels. Boundary (4), value side: " ++
        "`valueFrobeniusPower` with unit / multiplication / degree laws; the divisor " ++
        "side remains blocked by the missing sharp divisorial monoid (see " ++
        "`IUT-II.prime-strips-frobenioid-skeleton-cards`). Boundary (1) evaluated: the " ++
        "concrete local D-prime-strips have trivial geometric kernel " ++
        "(`localDPrimeStrip_geometric_eq_bot`, `finiteLocalDPrimeStrip_geometric_eq_bot`); " ++
        "the nontrivial geometric fundamental group of the source is not available " ++
        "(Mathlib has no etale fundamental group of a curve). Boundary (2) card kept: " ++
        "the completion carrier exists (`numberFieldPlaceCompletionCarrier`) but the " ++
        "V_K transport / rho_v normalization is absent at the prime-strip layer. Deep " ++
        "structure (structure equivalence and restrictions, [FrdI] Cor 4.11) is out of " ++
        "scope of this round; the upstream pointer was used for shape comparison only. " ++
        "REQ-3 consumer-side supply consumed via the constructed-core docking " ++
        "(Section 5); the source Frobenius carrier remains an exact card." ++
        "REQ-2 consumer-side supply consumed (Section 6); the image " ++
        "identifications v((Qp)^x) = Q and the degree image remain " ++
        "additional consumer hypotheses."
    dependsOn :=
      [ "IUT-II.prime-strips-frobenioid-link-layer",
        "IUT-II.prime-strips-frobenioid-skeleton-cards" ] }

end LeanFormal.IUT.Audit
