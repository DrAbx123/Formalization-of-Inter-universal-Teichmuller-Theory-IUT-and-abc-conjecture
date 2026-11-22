import LeanFormal.IUT.IUTII.Kummer.VerticalLogKummer
import LeanFormal.IUT.IUTIII.Theorem311.Indeterminacy.UpperSemi
import LeanFormal.IUT.IUTII.Kummer.K1K2BoundaryReduction
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellCodomainClosure
import LeanFormal.IUT.IUTII.Frobenioid.PrimeStripsFrobenioidLinks
import LeanFormal.IUT.IUTII.Kummer.RootRealization
import Mathlib.Tactic

set_option linter.unusedVariables false

/-!
  # K1/K2 realization draft (skeleton, run k1k2-realization-20261016)

  Minimal compilable skeleton: it packages the ordered-layer Kummer contract
  (`VerticalLogKummerCorrespondence`, IUT-II layer) into the K1 vertical
  carrier `UpperSemiCorrespondence Nat D` by an explicit, cast-free
  log-iterate sequence.  Route K1-alpha of the actual-construction attempt.

  Subsequent iterations extend this draft (log-shell card route, K2
  FrobenioidValueKernel bridge) before installation under
  LeanFormal/IUT/IUTIII/Theorem311/.
-/

namespace LeanFormal.IUT

universe u v

/-- Iterated log-link sequence in a Nat-indexed fibre family, starting at a
chosen base element `x0 : F 0`.  Recursion on the target index keeps the
definition cast-free: `kummerLogIterate log x0 (n + 1)` is definitionally
`log n (kummerLogIterate log x0 n)`. -/
def kummerLogIterate {F : Nat -> Type u} (log : ∀ m, F m -> F (m + 1))
    (x0 : F 0) : (m : Nat) -> F m
  | 0 => x0
  | n + 1 => log n (kummerLogIterate log x0 n)

@[simp] theorem kummerLogIterate_succ {F : Nat -> Type u}
    (log : ∀ m, F m -> F (m + 1)) (x0 : F 0) (n : Nat) :
    kummerLogIterate log x0 (n + 1) = log n (kummerLogIterate log x0 n) :=
  rfl

/-- Route K1-alpha carrier: the singleton upper-semi correspondence carried by
the Kummer values along the iterated log-link sequence.  The upper-semi law is
the ordered-layer compatibility `kummer m x ≤ kummer (m + 1) (log m x)`
iterated along `kummerLogIterate`. -/
def upperSemiOfKummerLine {F : Nat -> Type u} {B : Type v} [Preorder B]
    (log : ∀ m, F m -> F (m + 1)) (kummer : ∀ m, F m -> B)
    (hcompat : ∀ m x, kummer m x ≤ kummer (m + 1) (log m x))
    (x0 : F 0) : UpperSemiCorrespondence Nat B where
  image m := {kummer m (kummerLogIterate log x0 m)}
  upper := by
    intro a b hab z hz
    have hstep : ∀ m, kummer m (kummerLogIterate log x0 m) ≤
        kummer (m + 1) (kummerLogIterate log x0 (m + 1)) := by
      intro m
      rw [kummerLogIterate_succ]
      exact hcompat m (kummerLogIterate log x0 m)
    have hmono : ∀ n, a ≤ n ->
        kummer a (kummerLogIterate log x0 a) ≤
          kummer n (kummerLogIterate log x0 n) := by
      intro n han
      induction han with
      | refl => exact le_rfl
      | step hle ih => exact ih.trans (hstep _)
    have hz' : z = kummer a (kummerLogIterate log x0 a) := by
      simpa using hz
    subst hz'
    exact ⟨kummer b (kummerLogIterate log x0 b), by simp, hmono b hab⟩

namespace VerticalLogKummerCorrespondence

variable (K : VerticalLogKummerCorrespondence) (x0 : K.F 0)

/-- The ordered-layer contract carried into the K1 vertical slot. -/
def verticalUpperSemi : UpperSemiCorrespondence Nat K.D :=
  upperSemiOfKummerLine K.log K.kummer K.upperSemi x0

@[simp] theorem verticalUpperSemi_image (m : Nat) :
    (K.verticalUpperSemi x0).image m =
      {K.kummer m (kummerLogIterate K.log x0 m)} := rfl

theorem verticalUpperSemi_upper (m n : Nat) (hmn : m ≤ n) (z : K.D)
    (hz : z ∈ (K.verticalUpperSemi x0).image m) :
    ∃ w, w ∈ (K.verticalUpperSemi x0).image n ∧ z ≤ w :=
  (K.verticalUpperSemi x0).upper hmn z hz

end VerticalLogKummerCorrespondence


/-! ## E1: K1 image cards from a log-shell ray presentation -/

namespace K1K2Realization

noncomputable section

open Theorem311Source
open Theorem311Source.SourceHodgeTheaterBridge
open Theorem311Source.SourceDependencyChain

variable {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
variable [AddGroup Label] [Preorder Choice]

/-- E1 presentation: every possible image is the log-shell cut by a height ray
`{x | h c <= x}`.  Object: the packet `Q`, a candidate log-shell set `L` and a
height function `h`.  Consumers: the three K1 image cards below and, through
`K1K2BoundaryReduction.k1FromImageCards`, the K1 boundary record. -/
def LogShellRayPresentation {P : SourceLGPProcession l Label Choice}
    (Q : SourcePacketRealization P) (L : Set Real) (h : Choice → Real) : Prop :=
  ∀ c, Q.possibleImage c = L ∩ Set.Ici (h c)

/-- E1-a: under the ray presentation, N1 (`nonarchimedeanImageInclusion`) is
exactly the height law "heights do not increase under ind3". -/
theorem nonarchimedeanImageInclusion_of_logShellPresentation
    {P : SourceLGPProcession l Label Choice} (Q : SourcePacketRealization P)
    (L : Set Real) (h : Choice → Real)
    (hpres : LogShellRayPresentation Q L h)
    (hind3 : ∀ (m : Nat) (c : Choice), h (P.ind3 m c) ≤ h c) :
    K1K2BoundaryReduction.nonarchimedeanImageInclusion P Q := by
  intro m c z hz
  rw [hpres c] at hz
  rw [hpres (P.ind3 m c)]
  exact ⟨hz.1, (hind3 m c).trans hz.2⟩

/-- E1-b: under the ray presentation, A1 (`archimedeanTargetLift`) follows from
up-unboundedness of the log-shell set `L`. -/
theorem archimedeanTargetLift_of_logShellPresentation
    {P : SourceLGPProcession l Label Choice} (Q : SourcePacketRealization P)
    (L : Set Real) (h : Choice → Real)
    (hpres : LogShellRayPresentation Q L h)
    (hunbounded : ∀ x : Real, ∃ y ∈ L, x ≤ y) :
    K1K2BoundaryReduction.archimedeanTargetLift P Q := by
  intro m c z _
  obtain ⟨y, hyL, hy⟩ := hunbounded (max z (h c))
  refine ⟨y, ?_, le_trans (le_max_left z (h c)) hy⟩
  rw [hpres c]
  exact ⟨hyL, le_trans (le_max_right z (h c)) hy⟩

/-- E1-c: under the ray presentation, N2 (`ind3ImageWellDefined`) follows from
ray separation of `L` and the law that `ind3` respects height classes. -/
theorem ind3ImageWellDefined_of_logShellPresentation
    {P : SourceLGPProcession l Label Choice} (Q : SourcePacketRealization P)
    (L : Set Real) (h : Choice → Real)
    (hpres : LogShellRayPresentation Q L h)
    (hsep : ∀ x y : Real, L ∩ Set.Ici x = L ∩ Set.Ici y → x = y)
    (hclass : ∀ (m : Nat) (c c' : Choice), h c = h c' →
      h (P.ind3 m c) = h (P.ind3 m c')) :
    K1K2BoundaryReduction.ind3ImageWellDefined P Q := by
  intro m c c' hcc'
  rw [hpres c, hpres c'] at hcc'
  have hh : h c = h c' := hsep _ _ hcc'
  calc Q.possibleImage (P.ind3 m c)
      = L ∩ Set.Ici (h (P.ind3 m c)) := hpres (P.ind3 m c)
    _ = L ∩ Set.Ici (h (P.ind3 m c')) := by rw [hclass m c c' hh]
    _ = Q.possibleImage (P.ind3 m c') := (hpres (P.ind3 m c')).symm

/-- E1-d: the K1 boundary assembled from the presentation route, reusing the
frozen card assembly `K1K2BoundaryReduction.k1FromImageCards`; the labelled
Kummer slot is passed through unchanged. -/
def k1BoundaryOfLogShellPresentation
    (P : SourceLGPProcession l Label Choice) (Q : SourcePacketRealization P)
    (L : Set Real) (h : Choice → Real)
    (hpres : LogShellRayPresentation Q L h)
    (hind3 : ∀ (m : Nat) (c : Choice), h (P.ind3 m c) ≤ h c)
    (hunbounded : ∀ x : Real, ∃ y ∈ L, x ≤ y)
    (hsep : ∀ x y : Real, L ∩ Set.Ici x = L ∩ Set.Ici y → x = y)
    (hclass : ∀ (m : Nat) (c c' : Choice), h c = h c' →
      h (P.ind3 m c) = h (P.ind3 m c'))
    (κ : ∀ c : Choice, LabelledKummerIso Choice Choice) :
    K1VerticalBoundary P Q :=
  K1K2BoundaryReduction.k1FromImageCards P Q
    (nonarchimedeanImageInclusion_of_logShellPresentation Q L h hpres hind3)
    (ind3ImageWellDefined_of_logShellPresentation Q L h hpres hsep hclass)
    (archimedeanTargetLift_of_logShellPresentation Q L h hpres hunbounded)
    κ

/-! ### E1 log-shell link: Kierkegaard datum over `Real` -/

/-- The carrier `SourceLogShellDatum` with coordinate field fixed to `Real`, so
that `logShell` is a `Set Real` consumable by the presentation above. -/
def logShellDatumOverReal (p : Nat) (hp : Nat.Prime p) {U : Type} [CommGroup U]
    (invariants : Submonoid U) (logMap : U →* Multiplicative Real) :
    SourceLogShellDatum where
  p := p
  hp := hp
  K := Real
  Units := U
  invariants := invariants
  logMap := logMap

/-- E1 log-shell fact: under the datum presentation, possible images are
subsets of the log-shell `D.logShell` (the faithful shape "possible images lie
in log-shells"). -/
theorem possibleImage_subset_logShell_of_datumPresentation
    {P : SourceLGPProcession l Label Choice} (Q : SourcePacketRealization P)
    (p : Nat) (hp : Nat.Prime p) {U : Type} [CommGroup U]
    (invariants : Submonoid U) (logMap : U →* Multiplicative Real)
    (h : Choice → Real)
    (hpres : LogShellRayPresentation Q
      (logShellDatumOverReal p hp invariants logMap).logShell h) :
    ∀ c, Q.possibleImage c ⊆
      (logShellDatumOverReal p hp invariants logMap).logShell := by
  intro c
  rw [hpres c]
  exact Set.inter_subset_left

/-- E1 consumer: the Kierkegaard closure theorem
(`codomainKummerContained_of_invariants_eq_top`, SHA CE12CC99) applies to the
over-`Real` datum with top invariants, giving the domain inclusion
`unitLayer ⊆ logShell` on the real-coordinate carrier. -/
theorem codomainKummerContained_of_top_invariants_overReal
    (p : Nat) (hp : Nat.Prime p) {U : Type} [CommGroup U]
    (logMap : U →* Multiplicative Real) :
    (logShellDatumOverReal p hp (⊤ : Submonoid U) logMap).codomainKummerContained :=
  SourceLogShellDatum.codomainKummerContained_of_invariants_eq_top _ rfl

/-! ## E2: K2 from the IUT-II Frobenioid kernel link layer -/

universe ux uy

/-- E2-a: the IUT-II Frobenioid value kernel fills the frozen Proposition 3.7
record field-for-field.  No field is added or weakened; the conversion is the
identity on the degree, realification, effectiveness and transport data. -/
def sourceProposition37FrobenioidOfValueKernel {X : Type ux} [CommMonoid X]
    (V : FrobenioidValueKernel X) : SourceProposition37Frobenioid X where
  degree := V.degree
  realification := V.realification
  realification_mul := V.realification_mul
  degree_realification := V.degree_realification
  unit := V.unit
  unit_realification := V.unit_realification
  effective := V.effective
  effective_proved := V.effective_proved
  transport := V.transport
  transport_degree := V.transport_degree

/-- E2-b: K2 boundary assembled from the IUT-II link layer (kernels converted to
the frozen records) plus the comparison package with its four alignment
equations and the K1 vertical carrier.  Realifications are the link-layer
derivations, not re-supplied. -/
def k2FrobenioidBoundaryOfLinkLayer
    (R : SourceTheorem311Realization l Label Choice)
    (K : K1VerticalBoundary R.procession R.packet)
    {X : Type ux} {Y : Type uy} [CommMonoid X] [CommMonoid Y]
    (L : PrimeStripFrobenioidLinkLayer X Y)
    (comparison : SourceProposition310Comparison Choice Choice)
    (comparison_local : comparison.localMap =
      R.evaluation.evaluation.localMap)
    (comparison_global : comparison.globalMap =
      R.evaluation.evaluation.globalMap)
    (comparison_lower : comparison.lower =
      R.evaluation.evaluation.localComp)
    (comparison_upper : comparison.upper =
      R.evaluation.evaluation.globalComp) :
    K2FrobenioidBoundary R K X Y where
  localFrobenioid := sourceProposition37FrobenioidOfValueKernel L.localFrobenioid
  globalFrobenioid := sourceProposition37FrobenioidOfValueKernel L.globalFrobenioid
  modMap := L.modMap
  MODMap := L.MODMap
  mod_degree := fun x => L.mod_degree x
  MOD_degree := fun x => L.MOD_degree x
  mod_realification := fun x => L.mod_realification x
  MOD_realification := fun x => L.MOD_realification x
  mod_transport := fun x => L.mod_transport x
  MOD_transport := fun x => L.MOD_transport x
  comparison := comparison
  comparison_local := comparison_local
  comparison_global := comparison_global
  comparison_lower := comparison_lower
  comparison_upper := comparison_upper
  upperSemi := K.vertical
  upperSemi_eq_k1 := rfl

/-- E2-c (consumer): in the single-place finite model the `mod` direction is the
proved card `finitePlaceModDirectionCard`; hence the K2 record is inhabited from
the frozen inputs plus the conditional `MODDirectionCard` (Card MD2) and the
comparison/evaluation alignment. -/
theorem k2FrobenioidBoundary_nonempty_of_finitePlaceModel
    (R : SourceTheorem311Realization l Label Choice)
    (K : K1VerticalBoundary R.procession R.packet)
    (s : Finset RationalPrimePlace)
    (v₀ : {v : RationalPrimePlace // v ∈ s})
    (hMOD : MODDirectionCard (localIntegralPlaceFrobenioidValueKernel v₀.1)
      (finitePlaceFrobenioidValueKernel s))
    (comparison : SourceProposition310Comparison Choice Choice)
    (comparison_local : comparison.localMap =
      R.evaluation.evaluation.localMap)
    (comparison_global : comparison.globalMap =
      R.evaluation.evaluation.globalMap)
    (comparison_lower : comparison.lower =
      R.evaluation.evaluation.localComp)
    (comparison_upper : comparison.upper =
      R.evaluation.evaluation.globalComp) :
    Nonempty (K2FrobenioidBoundary R K
      (frobenioidLinkIntegralStrip.Mon v₀.1) (FinitePlaceValueFamily s)) := by
  obtain ⟨L⟩ := singlePlaceLinkLayer_nonempty_of_MODCard s v₀ hMOD
  exact ⟨k2FrobenioidBoundaryOfLinkLayer R K L comparison comparison_local
    comparison_global comparison_lower comparison_upper⟩

/-! ## E3: AdjoinRoot conditional Kummer bijection -/

/-- E3-a: an injective AdjoinRoot realization yields a labelled Kummer iso from
the adjoined quotient to the range of the lift.  Injectivity of the lift is the
named missing object (irreducibility/degree of the Kummer polynomial); the
kernel provides only the lift, its root equations, and root non-vanishing. -/
def labelledKummerIsoOfInjectiveLift {Fbase : Type*} [Field Fbase]
    (D : KummerPolynomialData Fbase) (Lt : Type*) [Field Lt] [Algebra Fbase Lt]
    (Radj : AdjoinRootEmbedding D Lt)
    (hinj : Function.Injective (Radj.lift D Lt)) :
    LabelledKummerIso D.Adjoined (Set.range (Radj.lift D Lt)) where
  map a := ⟨Radj.lift D Lt a, Set.mem_range_self a⟩
  inverse b := Classical.choose b.property
  left_inverse := by
    intro a
    apply hinj
    exact Classical.choose_spec (Set.mem_range_self (f := Radj.lift D Lt) a)
  right_inverse := by
    intro b
    apply Subtype.ext
    exact Classical.choose_spec b.property
  label := fun _ => 0
  label_map := fun _ => rfl

/-- E3-b: application to the actual local Kummer root realization: the labelled
Kummer iso on the adjoined quotient of `localKummerPolynomialFor p n` exists
under injectivity of its lift into the algebraic closure of `Q_[p]`. -/
theorem labelledKummerIso_nonempty_of_localKummerRootRealizationFor
    (p n : Nat) [Fact (Nat.Prime p)] (hn : 0 < n)
    (hinj : Function.Injective
      ((localKummerRootRealizationFor p n hn).lift
        (localKummerPolynomialFor p n hn) (AlgebraicClosure ℚ_[p]))) :
    Nonempty (LabelledKummerIso (localKummerPolynomialFor p n hn).Adjoined
      (Set.range ((localKummerRootRealizationFor p n hn).lift
        (localKummerPolynomialFor p n hn) (AlgebraicClosure ℚ_[p])))) :=
  ⟨labelledKummerIsoOfInjectiveLift (localKummerPolynomialFor p n hn)
    (AlgebraicClosure ℚ_[p]) (localKummerRootRealizationFor p n hn) hinj⟩

/-- E3-c: on an exponent-two root set of a ring element, negation is a
non-identity labelled Kummer iso (`(-x)^2 = x^2`); a concrete non-identity
inhabitant of the Kummer slot built from root data. -/
def rootNegationLabelledKummerIso {Aring : Type*} [Ring Aring] (a : Aring) :
    LabelledKummerIso {x : Aring // x ^ 2 = a} {x : Aring // x ^ 2 = a} where
  map x := ⟨-x.1, by rw [pow_two, neg_mul_neg, ← pow_two]; exact x.2⟩
  inverse x := ⟨-x.1, by rw [pow_two, neg_mul_neg, ← pow_two]; exact x.2⟩
  left_inverse := by intro x; apply Subtype.ext; simp
  right_inverse := by intro x; apply Subtype.ext; simp
  label := fun _ => 0
  label_map := fun _ => rfl

end

end K1K2Realization

end LeanFormal.IUT
