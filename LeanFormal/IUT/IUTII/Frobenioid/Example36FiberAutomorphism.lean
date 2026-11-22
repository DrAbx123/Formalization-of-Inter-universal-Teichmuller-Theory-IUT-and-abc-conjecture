import LeanFormal.IUT.IUTII.Frobenioid.Example36ContinuousGaloisSets
import LeanFormal.IUT.IUTII.Frobenioid.Example36GSetToEtaleAlgebra
import LeanFormal.IUT.IUTII.Frobenioid.Example36FiniteEtaleFiber
import LeanFormal.IUT.IUTII.Frobenioid.Example36EtaleCoverFoundations
import LeanFormal.IUT.Audit.Status
import Mathlib.CategoryTheory.Galois.IsFundamentalgroup
import Mathlib.Tactic

set_option linter.unusedSectionVars false

/-!
# Foundation F1g: automorphisms of the finite-etale fiber functor versus G_K

The actual finite-etale fiber functor at the separable closure
F = CommAlgCat.FiniteEtale.fiber K (SeparableClosure K) : (FiniteEtale K)^op -> FintypeCat
is defined, together with the actual action of the absolute Galois group
G_K = Iut.AbsoluteGaloisProfinite K = Gal(SeparableClosure K / K) on each fiber F.obj X
by postcomposition with the induced K-algebra automorphism of the separable closure,
and the resulting natural comparison monoid homomorphism
absoluteGaloisToFiberAut : G_K ->* Aut F (the direction opposite to the standard
evaluation map Aut F -> G_K; its inverse, when bijective, is the evaluation map).

## F1g-cont update: unconditional injectivity and the exact missing lemma

The comparison map is now proved INJECTIVE unconditionally
(absoluteGaloisToFiberAut_injective), using the actual finite-etale algebras
`K[x]` (adjoin of a single element) and the actual finite-etale instance
`algebraEtale_of_finiteDimensional_isSeparable` from
Example36GSetToEtaleAlgebra.  The single missing lemma is now frozen exactly as
FiberAutomorphismSurjectivityCard (surjectivity of the comparison map); given
it, fiberAutMulEquivOfSurjective gives the group isomorphism
Aut(fieldFiber K) ≃* G_K.  The conditional Galois-category route implies the
card (fiberAutomorphismSurjectivityCard_of_fundamentalGroup), so the only
genuinely missing data is that surjectivity, equivalently the functoriality/
equivalence of the actual object-and-fiber correspondence of
Example36GSetToEtaleAlgebra.

Also proved here for real: the continuous-G_K-set model of the same fiber functor
(finiteContinuousGaloisSetFiber (Iut.AbsoluteGaloisProfinite K)) has automorphism
group isomorphic to G_K, by the tree's IsFundamentalGroup instance and Mathlib's
Galois-category fundamental-group theorem (PreGaloisCategory.toAutMulEquiv).

## What remains missing (exact categorical card)

For the finite-etale fiber functor itself, the required Galois-category structure on
(CommAlgCat.FiniteEtale K)^op is NOT available in Mathlib 4.32.2 (and is not faked
here): the exact missing instances are
* PreGaloisCategory ((CommAlgCat.FiniteEtale K)^op),
* PreGaloisCategory.FiberFunctor (fieldFiber K),
* PreGaloisCategory.IsFundamentalGroup (fieldFiber K) G_K.
Given these, Mathlib's toAutMulEquiv gives Aut (fieldFiber K) ≃* G_K, whose inverse
is the desired evaluation map; the conditional theorem
fieldFiberAutMulEquivOfFundamentalGroup below records exactly this reduction.
Equivalently, a FieldGaloisCorrespondence K (tree card) with fiber-functor
compatibility would supply the instances.  No curve Pi_1, no fake Galois category,
no source-faithfulness or theta/q/Tate claim.
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open CategoryTheory CommAlgCat

universe u

variable (K : Type u) [Field K]

/-! ## 1. The actual finite-etale fiber functor at the separable closure -/

/-- The actual finite-etale fiber functor at the separable closure of K. -/
noncomputable abbrev fieldFiber : (CommAlgCat.FiniteEtale.{u} K)ᵒᵖ ⥤ FintypeCat.{u} :=
  finiteEtaleFiber (K := K) (Ω := SeparableClosure K)

/-- The absolute Galois group carrier as an element of Gal(separably closed / K). -/
noncomputable def absoluteGaloisAlgEquiv (σ : ↥(Iut.AbsoluteGaloisProfinite K)) :
    SeparableClosure K ≃ₐ[K] SeparableClosure K :=
  σ

/-! ## 2. The actual action of G_K on the fibers of the fiber functor -/

/-- The absolute Galois group acts on the fiber Hom_K(A, Kbar) of each finite
etale K-algebra A by postcomposition with the induced K-automorphism of Kbar. -/
noncomputable instance fieldFiberMulAction (X : (CommAlgCat.FiniteEtale.{u} K)ᵒᵖ) :
    MulAction ↥(Iut.AbsoluteGaloisProfinite K) ((fieldFiber K).obj X) where
  smul σ f := show ((fieldFiber K).obj X).obj from
    ((absoluteGaloisAlgEquiv K σ).toAlgHom.comp
      (show (X.unop.obj →ₐ[K] SeparableClosure K) from f))
  one_smul f := by
    change (absoluteGaloisAlgEquiv K (1 : ↥(Iut.AbsoluteGaloisProfinite K))).toAlgHom.comp
      (show (X.unop.obj →ₐ[K] SeparableClosure K) from f) =
      (show (X.unop.obj →ₐ[K] SeparableClosure K) from f)
    ext a
    rfl
  mul_smul σ τ f := by
    change (absoluteGaloisAlgEquiv K (σ * τ)).toAlgHom.comp
      (show (X.unop.obj →ₐ[K] SeparableClosure K) from f) =
      ((absoluteGaloisAlgEquiv K σ).toAlgHom.comp
        (((absoluteGaloisAlgEquiv K τ).toAlgHom).comp
          (show (X.unop.obj →ₐ[K] SeparableClosure K) from f)))
    ext a
    rfl

/-- The action is natural: postcomposition commutes with the action of the fiber
functor on morphisms. -/
instance fieldFiberIsNaturalSMul :
    PreGaloisCategory.IsNaturalSMul (fieldFiber K) ↥(Iut.AbsoluteGaloisProfinite K) where
  naturality g X Y f x := by
    change (absoluteGaloisAlgEquiv K g).toAlgHom.comp ((fieldFiber K).map f x) =
      (fieldFiber K).map f ((absoluteGaloisAlgEquiv K g).toAlgHom.comp x)
    rfl

/-! ## 3. The natural comparison map G_K -> Aut(F) -/

/-- The natural monoid homomorphism from G_K to the automorphism group of the
finite-etale fiber functor, induced by the natural action on the fibers. -/
noncomputable def absoluteGaloisToFiberAut :
    ↥(Iut.AbsoluteGaloisProfinite K) →* Aut (fieldFiber K) :=
  PreGaloisCategory.toAut (fieldFiber K) ↥(Iut.AbsoluteGaloisProfinite K)

/-- Evaluation formula for the comparison map: an element of G_K acts on a fiber
by postcomposition. -/
@[simp]
theorem absoluteGaloisToFiberAut_hom_app_apply
    (σ : ↥(Iut.AbsoluteGaloisProfinite K)) (X : (CommAlgCat.FiniteEtale.{u} K)ᵒᵖ)
    (x : (fieldFiber K).obj X) :
    (absoluteGaloisToFiberAut K σ).hom.app X x = σ • x :=
  rfl

/-- The comparison map is injective whenever the action of G_K on all fibers is
faithful; in particular it is the canonical candidate map whose inverse is the
evaluation map Aut(F) -> G_K. -/
theorem absoluteGaloisToFiberAut_injective_of_faithful
    (h : ∀ (σ : ↥(Iut.AbsoluteGaloisProfinite K)),
      (∀ (X : (CommAlgCat.FiniteEtale.{u} K)ᵒᵖ) (x : (fieldFiber K).obj X),
        σ • x = x) → σ = 1) :
    Function.Injective (absoluteGaloisToFiberAut K) :=
by
  simpa [absoluteGaloisToFiberAut] using
    (PreGaloisCategory.toAut_injective_of_non_trivial
      (F := fieldFiber K) (G := ↥(Iut.AbsoluteGaloisProfinite K)) h)

/-! ## 3b. F1g-cont: unconditional injectivity via the actual fixed-field algebras -/

/-- **Faithfulness of the G_K action on the finite-etale fibers.**  If an element
sigma of G_K fixes every point of every fiber of the finite-etale fiber functor,
then sigma = 1.  Proof: for x in the separable closure, take the actual finite
etale K-algebra A = K[x] (the adjoin of x, finite etale via the actual
instance algebraEtale_of_finiteDimensional_isSeparable of
Example36GSetToEtaleAlgebra), and evaluate the fixed-point hypothesis on the
canonical point A -> Kbar; this forces sigma x = x for every x. -/
theorem absoluteGaloisToFiberAut_faithful
    (σ : ↥(Iut.AbsoluteGaloisProfinite K))
    (h : ∀ (X : (CommAlgCat.FiniteEtale.{u} K)ᵒᵖ) (x : (fieldFiber K).obj X),
      σ • x = x) :
    σ = 1 := by
  have hσ : absoluteGaloisAlgEquiv K σ =
      (1 : SeparableClosure K ≃ₐ[K] SeparableClosure K) := by
    ext x
    let A : IntermediateField K (SeparableClosure K) :=
      IntermediateField.adjoin K ({x} : Set (SeparableClosure K))
    haveI : FiniteDimensional K ↥A :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
    haveI : Algebra.IsSeparable K ↥A := inferInstance
    haveI : Algebra.Etale K ↥A :=
      GSetToEtaleAlgebra.algebraEtale_of_finiteDimensional_isSeparable K ↥A
    let X : (CommAlgCat.FiniteEtale.{u} K)ᵒᵖ :=
      Opposite.op (CommAlgCat.FiniteEtale.of K ↥A)
    have hpoint : ∀ a : ↥A,
        (absoluteGaloisAlgEquiv K σ) ((IntermediateField.val A) a) =
          (IntermediateField.val A) a := by
      intro a
      have ha := congrArg (fun (g : ((fieldFiber K).obj X).obj) =>
        (show ↥A →ₐ[K] SeparableClosure K from g) a)
        (h X (show ((fieldFiber K).obj X).obj from IntermediateField.val A))
      have hσa : (show ↥A →ₐ[K] SeparableClosure K from
          (σ • (show ((fieldFiber K).obj X).obj from IntermediateField.val A))) a =
          (absoluteGaloisAlgEquiv K σ) ((IntermediateField.val A) a) := rfl
      rw [hσa] at ha
      simpa using ha
    have hx : absoluteGaloisAlgEquiv K σ x = x := by
      simpa using hpoint ⟨x, IntermediateField.mem_adjoin_simple_self K x⟩
    simpa using hx
  exact hσ

/-- **The comparison map is injective, unconditionally.** -/
theorem absoluteGaloisToFiberAut_injective :
    Function.Injective (absoluteGaloisToFiberAut K) :=
  absoluteGaloisToFiberAut_injective_of_faithful (K := K)
    (absoluteGaloisToFiberAut_faithful K)

/-- **The exact missing lemma: surjectivity of the comparison map.**  Together
with the unconditional injectivity proved above, this single lemma gives the
group isomorphism Aut(fieldFiber K) ≃* G_K.  It is equivalent to the natural
automorphisms of the finite-etale fiber functor being exactly the
postcomposition actions by elements of G_K. -/
def FiberAutomorphismSurjectivityCard (K : Type u) [Field K] : Prop :=
  Function.Surjective (absoluteGaloisToFiberAut K)

/-- **From the single missing surjectivity lemma to Aut(F) ≃* G_K.** -/
noncomputable def fiberAutMulEquivOfSurjective
    (h : FiberAutomorphismSurjectivityCard K) :
    Aut (fieldFiber K) ≃* ↥(Iut.AbsoluteGaloisProfinite K) :=
  (MulEquiv.ofBijective (absoluteGaloisToFiberAut K)
    ⟨absoluteGaloisToFiberAut_injective K, h⟩).symm

/-- **The conditional Galois-category route implies the exact missing lemma.**
If the finite-etale fiber functor carried the Galois-category structure of
Mathlib, then Mathlib's fundamental-group theorem gives bijectivity of the
comparison map, hence its surjectivity.  Thus the three missing instances are
one sufficient source of FiberAutomorphismSurjectivityCard; no instance is
asserted here. -/
theorem fiberAutomorphismSurjectivityCard_of_fundamentalGroup
    [GaloisCategory ((CommAlgCat.FiniteEtale.{u} K)ᵒᵖ)]
    [PreGaloisCategory.FiberFunctor (fieldFiber K)]
    [PreGaloisCategory.IsFundamentalGroup (fieldFiber K)
      ↥(Iut.AbsoluteGaloisProfinite K)] :
    FiberAutomorphismSurjectivityCard K := by
  have hb := PreGaloisCategory.toAut_bijective (fieldFiber K)
    ↥(Iut.AbsoluteGaloisProfinite K)
  simpa [FiberAutomorphismSurjectivityCard, absoluteGaloisToFiberAut] using hb.surjective
/-! ## 4. The actual Galois-category model: continuous G_K-sets -/

/-- **The automorphism group of the continuous-G_K-set fiber functor is the
absolute Galois group.**  This is the actual Galois-category fundamental-group
theorem (tree instance plus Mathlib's PreGaloisCategory.toAutMulEquiv), applied
to the continuous finite G_K-set model of the fiber functor. -/
noncomputable def continuousGaloisSetFiberAutMulEquiv :
    Aut (finiteContinuousGaloisSetFiber (Iut.AbsoluteGaloisProfinite K)) ≃*
      ↥(Iut.AbsoluteGaloisProfinite K) := by
  haveI := finiteContinuousGaloisSets_galoisCategory (Iut.AbsoluteGaloisProfinite K)
  haveI := finiteContinuousGaloisSetFiber_fiberFunctor (Iut.AbsoluteGaloisProfinite K)
  haveI := finiteContinuousGaloisSetFiber_isFundamentalGroup (Iut.AbsoluteGaloisProfinite K)
  exact (PreGaloisCategory.toAutMulEquiv
    (finiteContinuousGaloisSetFiber (Iut.AbsoluteGaloisProfinite K))
    ↥(Iut.AbsoluteGaloisProfinite K)).symm

/-! ## 4b. Actual transport of Aut(continuous G_K-set fiber) through a category equivalence -/

/-- The automorphism group of the continuous-G_K-set fiber functor is invariant
under precomposition with the functor of an equivalence of categories.  This is
Mathlib's fully-faithful precomposition (left whiskering by an equivalence is an
equivalence of functor categories) applied to `Aut`. -/
noncomputable def continuousFiberAutMulEquivOfPrecomposition
    (E : (CommAlgCat.FiniteEtale.{u} K)ᵒᵖ ≌
      finiteContinuousGaloisSets (Iut.AbsoluteGaloisProfinite K)) :
    Aut (finiteContinuousGaloisSetFiber (Iut.AbsoluteGaloisProfinite K)) ≃*
      Aut (E.functor ⋙ finiteContinuousGaloisSetFiber
        (Iut.AbsoluteGaloisProfinite K)) := by
  let pre : (finiteContinuousGaloisSets (Iut.AbsoluteGaloisProfinite K) ⥤
      FintypeCat.{u}) ⥤
      ((CommAlgCat.FiniteEtale.{u} K)ᵒᵖ ⥤ FintypeCat.{u}) :=
    (CategoryTheory.Functor.whiskeringLeft
      (CommAlgCat.FiniteEtale.{u} K)ᵒᵖ
      (finiteContinuousGaloisSets (Iut.AbsoluteGaloisProfinite K))
      FintypeCat.{u}).obj E.functor
  haveI : pre.IsEquivalence := inferInstance
  haveI : pre.Full := inferInstance
  haveI : pre.Faithful := inferInstance
  exact (CategoryTheory.Functor.FullyFaithful.ofFullyFaithful (F := pre)).autMulEquivOfFullyFaithful
    (finiteContinuousGaloisSetFiber (Iut.AbsoluteGaloisProfinite K))

/-- **Actual group isomorphism `Aut(fieldFiber) ≃* Aut(continuous G_K-set fiber)`
from an actual equivalence of categories and a fiber-functor identification.**
This is the transport of the automorphism group along the equivalence
(FiniteEtale K)^op ≌ FiniteContinuousGaloisSetCategory K together with the
fiber-functor isomorphism.  It uses no frozen card and no fake categorical
instance: the equivalence and the fiber isomorphism are explicit data. -/
noncomputable def fiberAutMulEquivOfCategoryEquivalence
    (E : (CommAlgCat.FiniteEtale.{u} K)ᵒᵖ ≌
      finiteContinuousGaloisSets (Iut.AbsoluteGaloisProfinite K))
    (hF : fieldFiber K ≅ E.functor ⋙ finiteContinuousGaloisSetFiber
      (Iut.AbsoluteGaloisProfinite K)) :
    Aut (fieldFiber K) ≃*
      Aut (finiteContinuousGaloisSetFiber (Iut.AbsoluteGaloisProfinite K)) :=
  (Aut.autMulEquivOfIso hF).trans
    (continuousFiberAutMulEquivOfPrecomposition (K := K) E).symm

/-- **Actual group isomorphism `Aut(fieldFiber K) ≃* G_K`**, obtained by
transporting the actual theorem `Aut(continuous G_K-set fiber) ≃* G_K` along an
actual category equivalence and a fiber-functor identification.  This is the
unconditional-automorphism-group statement conditional only on the two explicit
pieces of the correspondence data; it is not a frozen card. -/
noncomputable def fiberAutMulEquivOfFiberCorrespondence
    (E : (CommAlgCat.FiniteEtale.{u} K)ᵒᵖ ≌
      finiteContinuousGaloisSets (Iut.AbsoluteGaloisProfinite K))
    (hF : fieldFiber K ≅ E.functor ⋙ finiteContinuousGaloisSetFiber
      (Iut.AbsoluteGaloisProfinite K)) :
    Aut (fieldFiber K) ≃* ↥(Iut.AbsoluteGaloisProfinite K) :=
  (fiberAutMulEquivOfCategoryEquivalence (K := K) E hF).trans
    (continuousGaloisSetFiberAutMulEquiv K)

/-- **The exact compatibility needed to convert the automorphism-group transport
into surjectivity of the specific comparison map.**  If the transported
automorphism group isomorphism intertwines the two comparison maps (i.e. the
fiber-functor identification is G_K-equivariant), then the comparison map
`absoluteGaloisToFiberAut` is surjective, hence an isomorphism. -/
theorem absoluteGaloisToFiberAut_surjective_of_compatible_autEquiv
    (e : Aut (fieldFiber K) ≃*
      Aut (finiteContinuousGaloisSetFiber (Iut.AbsoluteGaloisProfinite K)))
    (contEquiv : Aut (finiteContinuousGaloisSetFiber (Iut.AbsoluteGaloisProfinite K)) ≃*
      ↥(Iut.AbsoluteGaloisProfinite K))
    (hcompat : ∀ g : ↥(Iut.AbsoluteGaloisProfinite K),
      e (absoluteGaloisToFiberAut K g) = contEquiv.symm g) :
    Function.Surjective (absoluteGaloisToFiberAut K) := by
  intro t
  refine ⟨contEquiv (e t), ?_⟩
  apply e.injective
  rw [hcompat (contEquiv (e t)), MulEquiv.symm_apply_apply]
/-- **Actual implication: a compatible category equivalence + fiber-functor
identification gives surjectivity of the finite-etale comparison map.**  This is
the direct transport form of the actual theorem `Aut(continuous G_K-set fiber)
≃* G_K`; the hypothesis `hcompat` is exactly the G_K-equivariance of the actual
fiber-functor identification (comparison maps intertwined).  It is explicit data,
not a frozen card. -/
theorem absoluteGaloisToFiberAut_surjective_of_compatible_correspondence
    (E : (CommAlgCat.FiniteEtale.{u} K)ᵒᵖ ≌
      finiteContinuousGaloisSets (Iut.AbsoluteGaloisProfinite K))
    (hF : fieldFiber K ≅ E.functor ⋙ finiteContinuousGaloisSetFiber
      (Iut.AbsoluteGaloisProfinite K))
    (hcompat : ∀ g : ↥(Iut.AbsoluteGaloisProfinite K),
      fiberAutMulEquivOfCategoryEquivalence (K := K) E hF
          (absoluteGaloisToFiberAut K g) =
        (continuousGaloisSetFiberAutMulEquiv K).symm g) :
    Function.Surjective (absoluteGaloisToFiberAut K) :=
  absoluteGaloisToFiberAut_surjective_of_compatible_autEquiv (K := K)
    (fiberAutMulEquivOfCategoryEquivalence (K := K) E hF)
    (continuousGaloisSetFiberAutMulEquiv K) hcompat
/-! ## 5. Conditional identification for the finite-etale fiber functor -/

/-- **Conditional field-side fundamental-group identification.**  If the
finite-etale fiber functor carries the Galois-category structure of Mathlib
(PreGaloisCategory on (FiniteEtale K)^op, FiberFunctor fieldFiber, and
IsFundamentalGroup fieldFiber G_K), then Mathlib's fundamental-group theorem
gives Aut(fieldFiber) ≃* G_K; the inverse is the evaluation map Aut(F) -> G_K.
These three instances are exactly the missing axioms, recorded in the card. -/
noncomputable def fieldFiberAutMulEquivOfFundamentalGroup
    [GaloisCategory ((CommAlgCat.FiniteEtale.{u} K)ᵒᵖ)]
    [PreGaloisCategory.FiberFunctor (fieldFiber K)]
    [PreGaloisCategory.IsFundamentalGroup (fieldFiber K)
      ↥(Iut.AbsoluteGaloisProfinite K)] :
    Aut (fieldFiber K) ≃* ↥(Iut.AbsoluteGaloisProfinite K) :=
  (PreGaloisCategory.toAutMulEquiv (fieldFiber K)
    ↥(Iut.AbsoluteGaloisProfinite K)).symm

end Example36
end LeanFormal.IUT.IUTII.Frobenioid

namespace LeanFormal.IUT.Audit

/-- **Status card: automorphisms of the finite-etale fiber functor versus G_K.**

Actual in this module: the finite-etale fiber functor
fieldFiber K = CommAlgCat.FiniteEtale.fiber K (SeparableClosure K); the actual
action of the absolute Galois group G_K = Iut.AbsoluteGaloisProfinite K on each
fiber of fieldFiber K by postcomposition with the induced K-automorphism of the
separable closure (fieldFiberMulAction), with its naturality
(fieldFiberIsNaturalSMul); the resulting natural comparison monoid homomorphism
absoluteGaloisToFiberAut : G_K ->* Aut(fieldFiber K) with evaluation formula and
an injectivity criterion; and, on the continuous-G_K-set Galois-category model of
the same fiber functor, the actual isomorphism of groups
continuousGaloisSetFiberAutMulEquiv : Aut(finiteContinuousGaloisSetFiber G_K)
≃* G_K, obtained from the tree's IsFundamentalGroup instance and Mathlib's
PreGaloisCategory.toAutMulEquiv.

Missing (NOT constructed, NOT claimed): the Galois-category structure on
(CommAlgCat.FiniteEtale K)^op, i.e. the instances
GaloisCategory ((CommAlgCat.FiniteEtale K)^op) [equivalently PreGaloisCategory
plus a fiber functor], PreGaloisCategory.FiberFunctor (fieldFiber K), and
PreGaloisCategory.IsFundamentalGroup (fieldFiber K) G_K.  Mathlib 4.32.2 does not
provide the general-field Galois correspondence (it proves only the separably
closed base case CommAlgCat.FiniteEtale.equivOfIsSepClosed and the
Galois-category/fundamental-group theory for categories of actions and finite
continuous actions).  Given those instances, Mathlib's fundamental-group theorem
gives Aut(fieldFiber K) ≃* G_K, with inverse the desired evaluation map
Aut(F) -> G_K; this conditional reduction is proved as
fieldFiberAutMulEquivOfFundamentalGroup.  The tree card FieldGaloisCorrespondence
with fiber-functor compatibility would equivalently supply the instances; the
bijectivity of absoluteGaloisToFiberAut (faithfulness/surjectivity of the action
on all finite-etale fibers) is not proved here.

No curve Pi_1 identification; no fake Galois category, fiber functor or
fundamental-group instance; no source-faithfulness, theta-pilot, q-pilot or Tate
claim. -/
def example36FiberAutomorphism : Obligation :=
  { id := "IUT-I-II.example36-fiber-automorphism"
    source :=
      "IUT I, Definition 3.1(b),(d); IUT III, Example 3.6; foundation F1g " ++
        "fiber-functor automorphism row"
    status := VerificationStatus.interface
    note :=
      "Actual: fieldFiber K = CommAlgCat.FiniteEtale.fiber K " ++
        "(SeparableClosure K); actual action of G_K on every fiber by " ++
        "postcomposition, with naturality; the natural comparison map " ++
        "G_K ->* Aut(fieldFiber K), now proved INJECTIVE unconditionally via " ++
        "the actual finite-etale fixed-field algebras K[x] and the actual " ++
        "algebraEtale_of_finiteDimensional_isSeparable instance of " ++
        "Example36GSetToEtaleAlgebra; and on the continuous-G_K-set model the " ++
        "actual group isomorphism Aut(finiteContinuousGaloisSetFiber G_K) " ++
        "≃* G_K from the tree's IsFundamentalGroup instance and Mathlib's " ++
        "PreGaloisCategory.toAutMulEquiv. Missing: GaloisCategory " ++
        "((FiniteEtale K)^op) [or PreGaloisCategory plus FiberFunctor], " ++
        "FiberFunctor (fieldFiber K) and IsFundamentalGroup (fieldFiber K) " ++
        "G_K; given them Aut(fieldFiber K) ≃* G_K follows (conditional " ++
        "theorem fieldFiberAutMulEquivOfFundamentalGroup), with inverse the " ++
        "evaluation map. ADDITIONAL ACTUAL TRANSPORT (task-103 continuation): from " ++
        "an actual category equivalence E : (FiniteEtale K)^op ≌ " ++
        "FiniteContinuousGaloisSetCategory K together with a fiber-functor " ++
        "identification hF : fieldFiber K ≅ E.functor ⋙ continuous fiber, " ++
        "fiberAutMulEquivOfCategoryEquivalence transports Aut along the " ++
        "equivalence and fiberAutMulEquivOfFiberCorrespondence gives the " ++
        "actual group isomorphism Aut(fieldFiber K) ≃* G_K (no frozen card). " ++
        "Surjectivity of the SPECIFIC comparison map still needs the G_K-" ++
        "equivariance compatibility hcompat of the fiber identification; " ++
        "absoluteGaloisToFiberAut_surjective_of_compatible_autEquiv and " ++
        "absoluteGaloisToFiberAut_surjective_of_compatible_correspondence " ++
        "prove the exact implication from that compatibility. The exact " ++
        "mathematical obstruction is the construction of E, hF and hcompat " ++
        "from the actual fixed-field/orbit-decomposition data (task-78 " ++
        "naturality/fiber compatibility), not a categorical-card assertion. " ++
        "Mathlib 4.32.2 has only the separably closed base case and the " ++
        "action-category Galois theory. No curve pi1; no fake category/fiber " ++
        "functor; no source-faithfulness, theta/q/Tate claim."
    dependsOn := [] }

end LeanFormal.IUT.Audit
