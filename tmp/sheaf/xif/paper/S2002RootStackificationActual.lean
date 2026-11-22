import tmp.sheaf.xif.paper.S1997LTorsRootStackActual
import Mathlib.CategoryTheory.Sites.Descent.IsStack

/-!
# S2002: the l-tors root stackification -- exact first missing, and what it must contain

S1997 constructed the pointwise `l`-tors root prestack: the action groupoid of the
`l`-torsion units `mu_l` acting by multiplication on the thickened origin
`Z = Spec K[t]/t^l`.  It proved that the resulting category-valued pseudofunctor
`S1997RootPrestack K l.value` has a genuine order-`l` automorphism at the
origin over the cyclic test scheme `Spec K[Z/l]`.  The remaining input recorded
there is

  `S1997RootStackification K l = { stack, isStack, comparison, origin_faithful }`

i.e. an actual etale stack receiving the root prestack, with a comparison that
is faithful at the origin: the stackification of the root prestack.

## What this file proves

* `isStack_of_isPrestack_and_essSurj` (general): a category-valued prestack with
  effective descent for every covering sieve is a stack.  Mathlib's
  `Pseudofunctor.IsStack` is *defined* as the conjunction of `IsPrestack` and
  essential surjectivity of `toDescentData`; this lemma assembles the two
  halves, which Mathlib does not do.

* `S1997RootPrestack_isStack_iff`: for the root prestack itself,
  `IsStack` splits *exactly* into "descent of morphisms" and S1997's
  `S1997RootEffectiveDescent`.  Consequently
  `S1997RootStackification_of_prestack_descent`: prestack + effective descent
  solves the whole S1997 missing datum, with the identity comparison.

* `S2002_noFaithfulAtOrigin_of_discreteFiber` (no-go): if a pseudofunctor has
  subsingleton hom types in every fiber (a "discrete fiber"), then *no*
  comparison from the root prestack is faithful at the origin: the order-`l`
  origin automorphism is carried to an identity, contradicting
  `S1997CyclicOriginAut_ne_one`.  Hence every witness stack of the S1997 datum
  has a genuinely stacky fiber.  In particular
  `S2002_noRepresentableWitness`: no representable etale stack -- the only
  stacks currently constructed in this tree, via
  `representableEtalePresheaf_isSheaf` and the discrete-sheaf-to-stack bridge --
  can be the root stackification.

* `S2002_witness_aut`: for *any* witness of the S1997 datum the image of the
  origin automorphism in the stack is a nontrivial order-`l` automorphism; the
  fiber of the witness at the cyclic test scheme is not a subsingleton
  endomorphism type.

* `S2002RootStackificationDatum_iff` and
  `S2002RootStackificationDatum_implies_S1994`: the missing datum, written as an
  existential over test stacks, is exactly S1997's missing structure, and it
  still supplies S1994's stacky orbicurve.

## The exact first missing

`S2002RootStackificationDatum K l` is not proved here.  The honest content of the
missing is one mathematical construction, which the no-go results above show is
not available from the discrete/representable stack machinery of this tree:

  the quotient stack `[Z / mu_l]` of the thickened origin by the `l`-torsion
  units (`Z = Spec K[t]/t^l`, `mu_l = Spec K[t,t^{-1}]/(t^l - 1)`,
  `zeta . b = zeta * b`), whose `U`-points are `mu_l`-torsors `P` on the
  etale site of `U` together with a `mu_l`-equivariant map `P -> Z`, and
  whose comparison sends `b` to the trivial torsor with the constant
  equivariant map `b`.

Concretely (up to the usual dualizing conventions) its objects over an affine
`U = Spec A` are `(L, phi : L^{tensor l} = O_U, s in Gamma(U, oplus_{i<l} L^{tensor i}))`
with `s^l = 0`: the twisted version of `b^l = 0`.  The missing input is
therefore the usual root-stack formalism, none of which is in Mathlib:

1. `G`-torsors on a Grothendieck site for a sheaf of groups `G` (here the
   representable group scheme `mu_l`), and their descent: the stack of torsors;
2. the associated-twist construction and the stack of equivariant maps to `Z`;
3. effective descent (`IsStack`) for that quotient stack;
4. the comparison `S1997RootPrestack K l -> [Z / mu_l]` and its faithfulness at
   the origin, which is formal once 1-3 are available because the comparison
   is the identity on the trivial torsor.

Point 3 is not a Lean gap but a real mathematical statement.  For a field `K`
containing a nontrivial `l`-th root of unity and a Kummer cover (e.g. the
`l`-th power map on `G_m`, or a `mu_l`-Galois algebra such as `K[T]/(T^l - a)`),
the `l`-tors root prestack has a non-effective descent datum: locally
`b = 0`, with transition units the nontrivial `mu_l`-cocycle of the cover, which
is not a coboundary because every `mu_l`-valued unit on the cover is constant.
Hence `S1997RootEffectiveDescent` is expected to *fail*, and the prestack route
(`S1997RootStackification_of_prestack_descent`) is only a sufficient condition.
This Kummer computation is **not** formalized in this file; it is recorded here
as the reason why the missing input is the quotient stack, not the prestack.

No `IsStack` instance is postulated: the file only ever *uses* the class as a
hypothesis.  No sorry, admit or new axiom is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

namespace LeanFormal.IUT.XiFPaper.S2002RootStackificationActual

open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1997LTorsRootStackActual
open LeanFormal.IUT.XiFPaper.S1994KSideCovers

universe u

/-! ## 1. Assembling `IsStack` from its two halves -/

/-- A category-valued prestack with effective descent for every covering sieve
is a stack.  This is the converse of the definition of `Pseudofunctor.IsStack`
(Mathlib defines a stack as a prestack whose `toDescentData` is essentially
surjective for every covering sieve), which Mathlib does not state. -/
theorem isStack_of_isPrestack_and_essSurj {C : Type*} [Category* C]
    {J : GrothendieckTopology C}
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat)
    (hpre : F.IsPrestack J)
    (heff : ∀ (S : C) (R : Sieve S), R ∈ J S →
      (F.toDescentData (fun i : R.arrows.category => i.obj.hom)).EssSurj) :
    F.IsStack J := by
  letI := hpre
  apply Pseudofunctor.IsStack.of_isStackFor
  intro S R hR
  have hff := (F.isPrestackFor' R hR).fullyFaithful
  exact ⟨{ faithful := hff.faithful, full := hff.full, essSurj := heff S R hR }⟩

/-! ## 2. The missing witness, and the no-go for discrete fibers -/

variable {K : Type u} [Field K] {l : PrimeGeFive}

/-- The pointwise condition that a category-valued pseudofunctor has only
subsingleton hom types, i.e. that it cannot see any stacky point.  This holds
for every discrete stack (a sheaf of types) and for every representable etale
stack, the two kinds of stacks constructed in this tree. -/
def S2002DiscreteFiber (Q : Iut.EtaleStackPseudofunctor K) : Prop :=
  ∀ (U : LocallyDiscrete (Iut.SchemeOverField K)ᵒᵖ) (X Y : Q.obj U),
    Subsingleton (X ⟶ Y)

/-- The cyclic test scheme `Spec K[Z/l]` as an object of the site. -/
def S2002CyclicPoint : LocallyDiscrete (Iut.SchemeOverField K)ᵒᵖ :=
  LocallyDiscrete.mk (Opposite.op (S1997CyclicScheme K l))

/-- Faithfulness at the origin of a comparison with a pseudofunctor, in the
concrete form used by the S1997 missing datum. -/
def S2002FaithfulAtOrigin (Q : Iut.EtaleStackPseudofunctor K)
    (e : Pseudofunctor.StrongTrans (S1997RootPrestack K l.value) Q) : Prop :=
  ∀ f : End (S1997CyclicOrigin K l),
    (e.app (S2002CyclicPoint (K := K) (l := l))).toFunctor.map f =
      𝟙 ((e.app (S2002CyclicPoint (K := K) (l := l))).toFunctor.obj
        (S1997CyclicOrigin K l)) →
    f = 𝟙 (S1997CyclicOrigin K l)

/-- The exact missing datum, written as an existential over test stacks: an
etale stack together with a comparison from the root prestack that is faithful
at the origin. -/
def S2002RootStackificationDatum : Prop :=
  ∃ (Q : Iut.EtaleStackPseudofunctor K) (_ : Q.IsStack (Iut.SchemeOverField.etaleTopology K))
    (e : Pseudofunctor.StrongTrans (S1997RootPrestack K l.value) Q),
    S2002FaithfulAtOrigin Q e

/-- The missing datum is exactly S1997's missing stackification structure. -/
theorem S2002RootStackificationDatum_iff :
    S2002RootStackificationDatum (K := K) (l := l) ↔ S1997RootStackificationMissing K l := by
  constructor
  · rintro ⟨Q, hQ, e, he⟩
    exact ⟨{ stack := Q, isStack := hQ, comparison := e, origin_faithful := he }⟩
  · rintro ⟨W⟩
    exact ⟨W.stack, W.isStack, W.comparison, W.origin_faithful⟩

/-- A pseudofunctor with discrete fibers can never receive the root prestack
with a comparison faithful at the origin: the order-`l` automorphism at the
origin is carried to an identity.  Hence any witness stack of the S1997 datum
is genuinely stacky (has a fiber with a nontrivial automorphism). -/
theorem S2002_noFaithfulAtOrigin_of_discreteFiber (Q : Iut.EtaleStackPseudofunctor K)
    (e : Pseudofunctor.StrongTrans (S1997RootPrestack K l.value) Q)
    (hQ : S2002DiscreteFiber Q) :
    ¬ S2002FaithfulAtOrigin Q e := by
  intro hfaith
  have hsub : Subsingleton
      (((e.app (S2002CyclicPoint (K := K) (l := l))).toFunctor.obj
        (S1997CyclicOrigin K l)) ⟶
       ((e.app (S2002CyclicPoint (K := K) (l := l))).toFunctor.obj
        (S1997CyclicOrigin K l))) :=
    hQ (S2002CyclicPoint (K := K) (l := l)) _ _
  haveI := hsub
  have himg : (e.app (S2002CyclicPoint (K := K) (l := l))).toFunctor.map
        (S1997CyclicOriginAutEnd K l) =
      𝟙 ((e.app (S2002CyclicPoint (K := K) (l := l))).toFunctor.obj
        (S1997CyclicOrigin K l)) :=
    Subsingleton.elim _ _
  exact S1997CyclicOriginAut_ne_one K l (hfaith _ himg)

/-- Every representable etale stack has discrete fibers: its fiber at `U` is
the discrete category of morphisms `U -> X`. -/
theorem S2002RepresentableDiscreteFiber (X : Iut.SchemeOverField K) :
    S2002DiscreteFiber (Iut.schemeRepresentableEtalePseudofunctor K X) := by
  intro U A B
  exact Discrete.instSubsingletonDiscreteHom A B

/-- Consequently no representable etale stack can be the root stackification. -/
theorem S2002_noRepresentableWitness (X : Iut.SchemeOverField K) :
    ¬ ∃ e : Pseudofunctor.StrongTrans (S1997RootPrestack K l.value)
        (Iut.schemeRepresentableEtalePseudofunctor K X),
        S2002FaithfulAtOrigin _ e := by
  rintro ⟨e, he⟩
  exact S2002_noFaithfulAtOrigin_of_discreteFiber _ e
    (S2002RepresentableDiscreteFiber X) he

/-! ## 3. The prestack / effective-descent split for the root prestack -/

/-- Mathlib's `IsStack` is the conjunction of `IsPrestack` (descent of
morphisms) and effective descent for every covering sieve.  For the root prestack
this splits the missing interface exactly in two: the `IsPrestack` half and
S1997's `S1997RootEffectiveDescent`. -/
theorem S1997RootPrestack_isStack_iff :
    (S1997RootPrestack K l.value).IsStack (Iut.SchemeOverField.etaleTopology K) ↔
      (S1997RootPrestack K l.value).IsPrestack (Iut.SchemeOverField.etaleTopology K) ∧
        S1997RootEffectiveDescent K l.value := by
  constructor
  · intro h
    refine ⟨h.toIsPrestack, ?_⟩
    intro U R hR
    exact Pseudofunctor.IsStack.essSurj_of_sieve (S1997RootPrestack K l.value) R hR
  · rintro ⟨hpre, heff⟩
    exact isStack_of_isPrestack_and_essSurj (S1997RootPrestack K l.value) hpre heff

/-- If the root prestack is already an etale stack then the missing datum is
solved, with the identity comparison. -/
theorem S1997RootStackification_of_isStack
    (h : (S1997RootPrestack K l.value).IsStack (Iut.SchemeOverField.etaleTopology K)) :
    S1997RootStackificationMissing K l := by
  refine ⟨{ stack := S1997RootPrestack K l.value
            isStack := h
            comparison := Pseudofunctor.StrongTrans.id _
            origin_faithful := ?_ }⟩
  intro f hf
  exact hf

/-- The prestack route made explicit: descent of morphisms plus effective
descent for the root prestack solves the S1997 missing datum. -/
theorem S1997RootStackification_of_prestack_descent
    (hpre : (S1997RootPrestack K l.value).IsPrestack (Iut.SchemeOverField.etaleTopology K))
    (heff : S1997RootEffectiveDescent K l.value) :
    S1997RootStackificationMissing K l :=
  S1997RootStackification_of_isStack (K := K) (l := l)
    ((S1997RootPrestack_isStack_iff (K := K) (l := l)).mpr ⟨hpre, heff⟩)

/-- Effective descent is *necessary* for the root prestack to be a stack: it is
exactly the essential-surjectivity half of `IsStack`. -/
theorem S1997RootEffectiveDescent_of_isStack
    (h : (S1997RootPrestack K l.value).IsStack (Iut.SchemeOverField.etaleTopology K)) :
    S1997RootEffectiveDescent K l.value :=
  ((S1997RootPrestack_isStack_iff (K := K) (l := l)).mp h).2



/-! ## 4. The root prestack is groupoid-valued -/

/-- The inverse morphism in the root fiber: the inverse unit, which is again an
`l`-torsion unit. -/
noncomputable def S2002RootHomInv {R : Type u} [CommRing R] {l : Nat}
    {x y : S1997RootObj R l} (f : S1997RootHom R l x y) : S1997RootHom R l y x where
  zeta := f.zeta⁻¹
  zeta_pow := by
    have h1 : f.zeta ^ l = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, f.zeta_pow, Units.val_one]
    have h2 : (f.zeta⁻¹ : Rˣ) ^ l = 1 := by
      rw [inv_pow, h1, inv_one]
    change ((f.zeta⁻¹ : Rˣ) : R) ^ l = 1
    rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]
  eq := by
    rw [show y.b = (f.zeta : R) * x.b from f.eq]
    have hunit : ((f.zeta⁻¹ : Rˣ) : R) * (f.zeta : R) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [← mul_assoc, hunit, one_mul]

/-- The inverse unit followed by the unit is the identity morphism. -/
theorem S2002RootHom_inv_comp {R : Type u} [CommRing R] {l : Nat}
    {x y : S1997RootObj R l} (f : S1997RootHom R l x y) :
    S1997RootHom.comp (S2002RootHomInv f) f = S1997RootHom.id y := by
  apply S1997RootHom.ext
  exact inv_mul_cancel f.zeta

/-- The unit followed by its inverse is the identity morphism. -/
theorem S2002RootHom_comp_inv {R : Type u} [CommRing R] {l : Nat}
    {x y : S1997RootObj R l} (f : S1997RootHom R l x y) :
    S1997RootHom.comp f (S2002RootHomInv f) = S1997RootHom.id x := by
  apply S1997RootHom.ext
  exact mul_inv_cancel f.zeta

/-- The root fiber is a groupoid: the morphisms `zeta` with `zeta^l = 1` are
units.  Hence the root prestack is a pseudofunctor into *groupoids*: its
stackification, if it exists, is a Deligne-Mumford-type stack and not a sheaf of
sets. -/
noncomputable instance S2002RootGroupoid (R : Type u) [CommRing R] (l : Nat) :
    Groupoid (S1997RootObj R l) where
  inv f := S2002RootHomInv f
  inv_comp f := S2002RootHom_inv_comp f
  comp_inv f := S2002RootHom_comp_inv f

/-- The root prestack takes values in groupoids at every test object. -/
@[implicit_reducible]
noncomputable def S2002RootPrestack_pointwise_groupoid
    (U : LocallyDiscrete (Iut.SchemeOverField K)ᵒᵖ) :
    Groupoid ((S1997RootPrestack K l.value).obj U) := by
  rw [S1997RootPrestack_obj]
  exact S2002RootGroupoid _ _

/-! ## 5. What every witness must contain -/

/-- The image point of the origin in a witness stack. -/
noncomputable def S2002WitnessImage (W : S1997RootStackification K l) :
    (W.stack.obj (S2002CyclicPoint (K := K) (l := l))) :=
  (W.comparison.app (S2002CyclicPoint (K := K) (l := l))).toFunctor.obj
    (S1997CyclicOrigin K l)

/-- The image in a witness stack of the order-`l` automorphism of the origin. -/
noncomputable def S2002WitnessAut (W : S1997RootStackification K l) :
    End (S2002WitnessImage W) :=
  (W.comparison.app (S2002CyclicPoint (K := K) (l := l))).toFunctor.map
    (S1997CyclicOriginAutEnd K l)

/-- Any witness of the missing datum carries the order-`l` origin automorphism
to a nontrivial order-`l` automorphism of the image point.  This is the
mathematical content the missing stackification has to deliver: a stacky point
of order `l` at the origin, not merely a point. -/
theorem S2002_witness_aut (W : S1997RootStackification K l) :
    S2002WitnessAut W ^ l.value = 1 ∧ S2002WitnessAut W ≠ 𝟙 (S2002WitnessImage W) := by
  constructor
  · have h := map_pow (S1997EndMap
      (W.comparison.app (S2002CyclicPoint (K := K) (l := l))).toFunctor
      (S1997CyclicOrigin K l)) (S1997CyclicOriginAutEnd K l) l.value
    have h' : S2002WitnessAut W ^ l.value =
        (W.comparison.app (S2002CyclicPoint (K := K) (l := l))).toFunctor.map
          ((S1997CyclicOriginAutEnd K l) ^ l.value) := h.symm
    rw [S1997CyclicOriginAut_pow K l] at h'
    have hid : (W.comparison.app (S2002CyclicPoint (K := K) (l := l))).toFunctor.map
        (𝟙 (S1997CyclicOrigin K l)) = 𝟙 (S2002WitnessImage W) :=
      (W.comparison.app (S2002CyclicPoint (K := K) (l := l))).toFunctor.map_id _
    exact h'.trans hid
  · intro h
    exact S1997CyclicOriginAut_ne_one K l
      (W.origin_faithful (S1997CyclicOriginAutEnd K l) h)

/-- No witness stack has discrete fibers: combining the no-go with the
faithfulness requirement. -/
theorem S2002_witness_not_discreteFiber (W : S1997RootStackification K l) :
    ¬ S2002DiscreteFiber W.stack :=
  fun h => S2002_noFaithfulAtOrigin_of_discreteFiber W.stack W.comparison h W.origin_faithful

/-- Every witness has a fiber at the cyclic test scheme whose endomorphism type
at the image of the origin is not a subsingleton: the required stack is
genuinely stacky, so it cannot be a discrete (= set-valued) stack. -/
theorem S2002_witness_end_nontrivial (W : S1997RootStackification K l) :
    ¬ Subsingleton (End (S2002WitnessImage W)) := by
  intro hsub
  haveI := hsub
  exact (S2002_witness_aut W).2 (Subsingleton.elim _ _)

/-- The local-trivialization model of an object of the root stackification at a
test scheme: a covering sieve together with a descent datum for the root
prestack over it.  Objects of the stackification are exactly these data up to
refinement; the file records the shape so that the missing construction has a
concrete target, but it is *not* claimed here that this is a stack. -/
structure S2002LocalRootDatum (U : Iut.SchemeOverField K) where
  /-- The covering sieve of the local trivialization. -/
  sieve : Sieve U
  /-- It is a covering sieve for the etale topology. -/
  mem : sieve ∈ Iut.SchemeOverField.etaleTopology K U
  /-- The root data over the sieve. -/
  datum : (S1997RootPrestack K l.value).DescentData
    (fun i : sieve.arrows.category => i.obj.hom)

/-- The tautological local trivialization of an object of the root prestack: the
trivial covering sieve with the descent datum of the object itself.  This is the
object-level shadow of the comparison from the root prestack to its
stackification. -/
noncomputable def S2002CanonicalLocalRootDatum (U : Iut.SchemeOverField K)
    (x : (S1997RootPrestack K l.value).obj (LocallyDiscrete.mk (Opposite.op U))) :
    S2002LocalRootDatum (K := K) (l := l) U where
  sieve := ⊤
  mem := GrothendieckTopology.top_mem (Iut.SchemeOverField.etaleTopology K) U
  datum := ((S1997RootPrestack K l.value).toDescentData
    (fun i : (⊤ : Sieve U).arrows.category => i.obj.hom)).obj x

/-! ## 6. Consumer: the missing datum still supplies S1994's stacky orbicurve -/

/-- The missing root stackification supplies S1994's stacky orbicurve: the
nontrivial order-`l` automorphism at the origin is transported into the stack and
realized as an actual hyperbolic orbicurve. -/
theorem S2002RootStackificationDatum_implies_S1994 {A : InitialThetaArithmeticData l}
    (h : S2002RootStackificationDatum (K := A.K) (l := l)) :
    S1994StackyOrbicurveMissing l A :=
  S1997FirstMissing_implies_S1994Stacky
    ((S2002RootStackificationDatum_iff (K := A.K) (l := l)).mp h)

/-- The same consequence for the S1997 missing datum, in the terminology of
this file. -/
theorem S2002_witness_implies_S1994 {A : InitialThetaArithmeticData l}
    (W : S1997RootStackification A.K l) : S1994StackyOrbicurveMissing l A :=
  S1997FirstMissing_implies_S1994Stacky ⟨W⟩

/-! ## 7. Axiom footprint -/

#print axioms isStack_of_isPrestack_and_essSurj
#print axioms S2002RootStackificationDatum_iff
#print axioms S2002_noFaithfulAtOrigin_of_discreteFiber
#print axioms S2002RepresentableDiscreteFiber
#print axioms S2002_noRepresentableWitness
#print axioms S1997RootPrestack_isStack_iff
#print axioms S1997RootStackification_of_isStack
#print axioms S1997RootStackification_of_prestack_descent
#print axioms S1997RootEffectiveDescent_of_isStack
#print axioms S2002RootHom_inv_comp
#print axioms S2002RootHom_comp_inv
#print axioms S2002RootPrestack_pointwise_groupoid
#print axioms S2002_witness_aut
#print axioms S2002_witness_not_discreteFiber
#print axioms S2002_witness_end_nontrivial
#print axioms S2002RootStackificationDatum_implies_S1994

end LeanFormal.IUT.XiFPaper.S2002RootStackificationActual
