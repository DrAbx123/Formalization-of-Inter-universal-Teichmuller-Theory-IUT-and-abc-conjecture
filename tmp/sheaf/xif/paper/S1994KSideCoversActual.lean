/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/
import tmp.sheaf.xif.paper.S1989KSideCoverActual
import tmp.sheaf.xif.paper.S1419D6NonterminalStackActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceTorsionRankOneQuotient

/-!
# S1994: the K-side covers -- the underlying isogeny kernel and the exact first missing

S1989 specified the paper-faithful K-side cover record KSideCoverActual
(actual X_K^-> -> X_K and C_K^-> -> C_K of degree l, the quotient
X_K^-> -> C_K^->, and the quotient square) and proved that no inhabitant is
constructed.  This file attacks the construction itself.

## What is constructed here (curves, not stacks)

* The actual K-side punctured elliptic curve

    S1994KCurve A = A.curve.baseChange A.K,

  i.e. the base change to K of the Mathlib Weierstrass model carried by the
  arithmetic input, with its puncture.

* The rank-one quotient geometry of IUT I, Definition 3.1(c) at K, from any
  K-side l-torsion basis B (in particular from clause (c)'s
  SourceClauseC.k_torsion_basis):

    S1994RankOneQuotient B : TorsionRankOneQuotientData l (S1994KCurve A).

* The **isogeny kernel line**: the kernel H of the quotient map, proved to be
  the span of a single nonzero torsion vector (S1994KernelLine_eq_span), and
  proved to have exactly l elements (S1994KernelLine_card).  A degree-l
  isogeny E_K^-> -> E_K is determined by its kernel, a subgroup of E_K[l] of
  order l; S1994IsogenyKernelDatum is that kernel datum, and
  S1994IsogenyKernelDatumOfClauseC produces it from production clause (c).

  The quotient curve E_K^-> = E_K / H and the isogeny itself are **not**
  constructed: Mathlib has no theory of isogenies of Weierstrass curves, no
  quotient of an elliptic curve by a finite subgroup, and no l-tors
  theta/Kummer cover of a punctured elliptic curve.  Nothing here fakes them.

## What is proved about the record

* **The S1989 label fields are vacuous.**  Iut.HyperbolicOrbicurve.Hom only
  sees stack.fiber, the finite-etale certificate only sees the two fibers and
  the map, and the degree predicate only sees the certificate.  Relabelling a
  cover object changes none of these data, so:

    Nonempty (KSideCoverActual l A S C) <-> Nonempty (KSideCoverUnlabelled l A S C)

  (S1994KSideCoverActual_iff_unlabelled), where KSideCoverUnlabelled is the
  same record with the two signature fields deleted.  Sharper: *any* two
  orbicurves over K, *any* finite-etale degree-l maps to the cores and *any*
  2-commutative square give the labelled record after relabelling
  (S1994labelledRecord_of_arbitrary_endpoints).  Consequently the S1989
  record is exactly "an actual finite-etale degree-l stack map to each core";
  it carries no l-tors geometry by itself.

* **The orbicurve construction used in this tree cannot be the paper's.**
  The actual orbicurves of S1419, S1726 and S1886 are built as
  realizedHyperbolicOrbicurve applied to a representable etale stack.  Such a
  stack has *discrete* fibers: every automorphism of every point is the identity
  (S1994RepresentableOrbicurve_aut_eq_id), so it has no stacky point of any
  order (S1994RepresentableOrbicurve_noAutOfOrder).  The paper's l-tors
  orbicurve has a point with automorphism group Z/l; therefore no
  representable construction can produce the paper's cover.  This is a
  machine-checked obstruction, not a failure to find a proof.

* The paper-faithful datum S1994PaperKSideCover is the S1989 record together
  with the honest stacky-point conditions (order l at the l-tors point of
  X_K^->, orders 2 and l on C_K^->).  S1994PaperKSideCoverMissing is the
  target; S1994FirstMissing names it over the production core.

## Exact first missing (dependency order)

1. S1994StackyOrbicurveMissing l A: an actual orbicurve over A.K with a point
   whose automorphism has order l.  Equivalently an actual non-representable
   etale stack over A.K (root stack / stackification at the origin).  Not
   available: the tree has IsStack only for representable (discrete) fibers
   (S1419), and the action-category colimit is only pointwise (S1971); the
   general quotient-stack route is S1964's open G1.
2. Nonempty (KSideCoverUnlabelled l A S C): actual finite-etale degree-l stack
   morphisms to the two K-cores with a 2-commutative square.  Their
   base-change presentations require the two-pullback witnesses of S1891 and
   S1892; the pasting/closure inputs are recorded there as missing.
3. The curve-level isogeny E_K^-> -> E_K with kernel the constructed line, and
   the identification of the l-tors cover with it.  The kernel datum is
   constructed here; the quotient curve/isogeny is not.

No sorry, admit, new axiom, True, PUnit, point-fiber substitution or
terminal-stack substitution is used.  No production definition is edited.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1200000

namespace LeanFormal.IUT.XiFPaper.S1994KSideCovers

universe u

open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1989KSideCover
open LeanFormal.IUT.XiFPaper.S1984KSideObjectAudit
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.N8Closure.DiscreteSheafIsStack
open LeanFormal.IUT.N8Closure.RepresentableStackIsStackConstructed
open scoped Pseudofunctor.StrongTrans

/-! ## 1. The actual K-side punctured elliptic curve -/

/-- The actual K-side punctured elliptic curve: the base change to K of the
Mathlib Weierstrass model of the arithmetic input. -/
noncomputable def S1994KCurve (l : PrimeGeFive) (A : InitialThetaArithmeticData l) :
    PuncturedEllipticCurve A.K :=
  A.curve.baseChange A.K

@[simp] theorem S1994KCurve_curve (l : PrimeGeFive) (A : InitialThetaArithmeticData l) :
    (S1994KCurve l A).curve = A.curve.curve.baseChange A.K := rfl

theorem S1994KCurve_base (l : PrimeGeFive) (A : InitialThetaArithmeticData l) :
    (S1994KCurve l A).curve = A.curve.curve.map (algebraMap A.F A.K) := rfl

/-! ## 2. The rank-one quotient and the isogeny-kernel line -/

section Line

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData l}

/-- The K-side l-torsion module of the actual K-side curve. -/
abbrev S1994KTorsion (l : PrimeGeFive) (A : InitialThetaArithmeticData l) :=
  (S1994KCurve l A).LTorsion l

/-- The finite-index two-dimensional torsion type of the K-side curve. -/
abbrev S1994TorsionBasis (l : PrimeGeFive) (A : InitialThetaArithmeticData l) :=
  (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value] S1994KTorsion l A

/-- The rank-one quotient of IUT I, Definition 3.1(c) at K, from a K-side
torsion basis. -/
noncomputable def S1994RankOneQuotient
    (B : S1994TorsionBasis l A) :
    TorsionRankOneQuotientData l (S1994KCurve l A) :=
  ⟨B⟩

/-- The kernel of the rank-one quotient map: the kernel datum of the
underlying degree-l isogeny E_K^-> -> E_K. -/
noncomputable def S1994KernelLine (B : S1994TorsionBasis l A) :
    Submodule (ZMod l.value) (S1994KTorsion l A) :=
  (S1994RankOneQuotient B).Kernel

theorem S1994KernelLine_def (B : S1994TorsionBasis l A) :
    S1994KernelLine B = LinearMap.ker (S1994RankOneQuotient B).quotientMap := rfl

theorem S1994memKernelLine (B : S1994TorsionBasis l A) (x : S1994KTorsion l A) :
    x ∈ S1994KernelLine B ↔ (B.symm x) 0 = 0 := by
  rw [S1994KernelLine, TorsionRankOneQuotientData.Kernel, LinearMap.mem_ker]
  simp [S1994RankOneQuotient, TorsionRankOneQuotientData.quotientMap,
    LinearMap.proj_apply, LinearEquiv.coe_toLinearMap]

/-- The generator of the kernel line: the second basis vector. -/
noncomputable def S1994KernelVector (B : S1994TorsionBasis l A) :
    S1994KTorsion l A :=
  B (Pi.single (1 : Fin 2) (1 : ZMod l.value) : Fin 2 → ZMod l.value)

theorem S1994KernelVector_ne_zero (B : S1994TorsionBasis l A) :
    S1994KernelVector B ≠ 0 := by
  intro h
  have h1 : (Pi.single (1 : Fin 2) (1 : ZMod l.value) : Fin 2 → ZMod l.value) = 0 := by
    rw [← LinearEquiv.symm_apply_apply B
      (Pi.single (1 : Fin 2) (1 : ZMod l.value) : Fin 2 → ZMod l.value)]
    show B.symm (S1994KernelVector B) = 0
    rw [h, map_zero]
  have h2 := congrFun h1 1
  have h3 : (1 : ZMod l.value) = 0 := by simpa using h2
  haveI := l.factPrime
  exact one_ne_zero h3

theorem S1994KernelVector_mem (B : S1994TorsionBasis l A) :
    S1994KernelVector B ∈ S1994KernelLine B := by
  rw [S1994memKernelLine]
  simp [S1994KernelVector, Pi.single_eq_of_ne (show (0 : Fin 2) ≠ 1 by decide)]

/-- The kernel is exactly the line spanned by the second basis vector. -/
theorem S1994KernelLine_eq_span (B : S1994TorsionBasis l A) :
    S1994KernelLine B =
      Submodule.span (ZMod l.value) {(S1994KernelVector B : S1994KTorsion l A)} := by
  apply le_antisymm
  · intro x hx
    rw [Submodule.mem_span_singleton]
    refine ⟨(B.symm x) 1, ?_⟩
    have hx0 : (B.symm x) 0 = 0 := (S1994memKernelLine B x).mp hx
    have hcoord : B.symm x =
        (B.symm x) 1 • (Pi.single (1 : Fin 2) (1 : ZMod l.value) : Fin 2 → ZMod l.value) := by
      funext i
      fin_cases i
      · show (B.symm x) 0 =
          ((B.symm x) 1 • (Pi.single (1 : Fin 2) (1 : ZMod l.value) : Fin 2 → ZMod l.value)) 0
        rw [Pi.smul_apply, Pi.single_eq_of_ne (show (0 : Fin 2) ≠ 1 by decide), smul_zero, hx0]
      · show (B.symm x) 1 =
          ((B.symm x) 1 • (Pi.single (1 : Fin 2) (1 : ZMod l.value) : Fin 2 → ZMod l.value)) 1
        rw [Pi.smul_apply, Pi.single_eq_same]
        simp
    calc (B.symm x) 1 • S1994KernelVector B
        = (B.symm x) 1 • B (Pi.single (1 : Fin 2) (1 : ZMod l.value)) := by
          rw [S1994KernelVector]
      _ = B ((B.symm x) 1 • (Pi.single (1 : Fin 2) (1 : ZMod l.value))) := by rw [map_smul]
      _ = B (B.symm x) := (congrArg B hcoord).symm
      _ = x := LinearEquiv.apply_symm_apply B x
  · intro x hx
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [S1994memKernelLine]
    have hsmul : B.symm (a • S1994KernelVector B) =
        a • (Pi.single (1 : Fin 2) (1 : ZMod l.value) : Fin 2 → ZMod l.value) := by
      rw [S1994KernelVector, map_smul, LinearEquiv.symm_apply_apply]
    rw [hsmul]
    simp [Pi.single_eq_of_ne (show (0 : Fin 2) ≠ 1 by decide)]

/-- The kernel line is a genuine line: a nonzero vector spans it. -/
theorem S1994KernelLine_line (B : S1994TorsionBasis l A) :
    ∃ v : S1994KTorsion l A, v ≠ 0 ∧
      S1994KernelLine B = Submodule.span (ZMod l.value) {v} :=
  ⟨S1994KernelVector B, S1994KernelVector_ne_zero B, S1994KernelLine_eq_span B⟩

theorem S1994smulKernelVector_eq (B : S1994TorsionBasis l A)
    {x : S1994KTorsion l A} (hx : x ∈ S1994KernelLine B) :
    (B.symm x) 1 • S1994KernelVector B = x := by
  have hx0 : (B.symm x) 0 = 0 := (S1994memKernelLine B x).mp hx
  have hcoord : B.symm x =
      (B.symm x) 1 • (Pi.single (1 : Fin 2) (1 : ZMod l.value) : Fin 2 → ZMod l.value) := by
    funext i
    fin_cases i
    · show (B.symm x) 0 =
        ((B.symm x) 1 • (Pi.single (1 : Fin 2) (1 : ZMod l.value) : Fin 2 → ZMod l.value)) 0
      rw [Pi.smul_apply, Pi.single_eq_of_ne (show (0 : Fin 2) ≠ 1 by decide), smul_zero, hx0]
    · show (B.symm x) 1 =
        ((B.symm x) 1 • (Pi.single (1 : Fin 2) (1 : ZMod l.value) : Fin 2 → ZMod l.value)) 1
      rw [Pi.smul_apply, Pi.single_eq_same]
      simp
  calc (B.symm x) 1 • S1994KernelVector B
      = (B.symm x) 1 • B (Pi.single (1 : Fin 2) (1 : ZMod l.value)) := by
        rw [S1994KernelVector]
    _ = B ((B.symm x) 1 • (Pi.single (1 : Fin 2) (1 : ZMod l.value))) := by rw [map_smul]
    _ = B (B.symm x) := (congrArg B hcoord).symm
    _ = x := LinearEquiv.apply_symm_apply B x

/-- The kernel line, as a type, is the coefficient ring. -/
noncomputable def S1994KernelEquiv (B : S1994TorsionBasis l A) :
    (S1994KernelLine B) ≃ ZMod l.value where
  toFun x := (B.symm x.1) 1
  invFun a :=
    ⟨a • S1994KernelVector B, by
      rw [S1994KernelLine_eq_span]
      exact Submodule.smul_mem _ a (Submodule.subset_span (Set.mem_singleton _))⟩
  left_inv x := by
    apply Subtype.ext
    exact S1994smulKernelVector_eq B x.2
  right_inv a := by
    show (B.symm (a • S1994KernelVector B)) 1 = a
    have hsmul : B.symm (a • S1994KernelVector B) =
        a • (Pi.single (1 : Fin 2) (1 : ZMod l.value) : Fin 2 → ZMod l.value) := by
      rw [S1994KernelVector, map_smul, LinearEquiv.symm_apply_apply]
    rw [hsmul]
    simp

/-- The isogeny kernel of the degree-l isogeny has exactly l elements. -/
theorem S1994KernelLine_card (B : S1994TorsionBasis l A) :
    Nat.card (S1994KernelLine B) = l.value :=
  calc Nat.card (S1994KernelLine B)
      = Nat.card (ZMod l.value) := Nat.card_congr (S1994KernelEquiv B)
    _ = l.value := by rw [Nat.card_eq_fintype_card, ZMod.card]

/-- The rank-one quotient of E_K[l] by the kernel line is of rank one. -/
theorem S1994rankOneQuotient_is_rank_one (B : S1994TorsionBasis l A) :
    Nonempty ((S1994RankOneQuotient B).Quotient ≃ₗ[ZMod l.value] ZMod l.value) :=
  TorsionRankOneQuotientData.quotient_is_rank_one (S1994RankOneQuotient B)

/-- The distinguished class of the rank-one quotient is nonzero and reads as 1
under the quotient equivalence (IUT I, Definition 3.1(c)). -/
theorem S1994rankOneQuotient_distinguished (B : S1994TorsionBasis l A) :
    Function.Surjective (S1994RankOneQuotient B).quotientMap ∧
      (S1994RankOneQuotient B).distinguishedClass ≠ 0 ∧
      (S1994RankOneQuotient B).quotientEquiv
        (S1994RankOneQuotient B).distinguishedClass = 1 :=
  TorsionRankOneQuotientData.source_rank_one_quotient_spec (S1994RankOneQuotient B)

/-- The underlying-geometry datum of the degree-l isogeny E_K^-> -> E_K: its
kernel, a line in E_K[l] with l elements.  This is the curve-level half of the
paper's l-tors cover that is available in the tree. -/
structure S1994IsogenyKernelDatum (l : PrimeGeFive) (A : InitialThetaArithmeticData l) where
  /-- The kernel line in the actual K-side l-torsion. -/
  line : Submodule (ZMod l.value) (S1994KTorsion l A)
  /-- The kernel of a degree-l isogeny has l elements. -/
  line_card : Nat.card (line) = l.value
  /-- It is a line: spanned by one nonzero torsion point. -/
  line_generated : ∃ v : S1994KTorsion l A, v ≠ 0 ∧
    line = Submodule.span (ZMod l.value) {v}

/-- The isogeny kernel datum attached to a K-side torsion basis. -/
noncomputable def S1994IsogenyKernelDatum_ofBasis (B : S1994TorsionBasis l A) :
    S1994IsogenyKernelDatum l A where
  line := S1994KernelLine B
  line_card := S1994KernelLine_card B
  line_generated := S1994KernelLine_line B

/-- The production K-side torsion basis of clause (c) gives the isogeny kernel
datum on the actual K-side curve. -/
noncomputable def S1994IsogenyKernelDatumOfClauseC
    {S : SourceSignQuotientData A}
    {C : SourceClauseA A S} {B : SourceClauseB A S C}
    (D : SourceClauseC A S C B) :
    S1994IsogenyKernelDatum l A :=
  S1994IsogenyKernelDatum_ofBasis (l := l) (A := A) D.k_torsion_basis

theorem S1994IsogenyKernelDatumOfClauseC_card
    {S : SourceSignQuotientData A}
    {C : SourceClauseA A S} {B : SourceClauseB A S C}
    (D : SourceClauseC A S C B) :
    Nat.card ((S1994IsogenyKernelDatumOfClauseC (A := A) D).line) = l.value :=
  (S1994IsogenyKernelDatumOfClauseC (A := A) D).line_card

end Line

/-! ## 3. Stacky points of an orbicurve -/

section Stacky

variable {F : Type u} [Field F]

/-- The U-points of an orbicurve: the objects of its fiber category at the
test scheme U. -/
abbrev S1994Point (X : Iut.HyperbolicOrbicurve F) (U : Iut.SchemeOverField F) : Type u :=
  ↑(X.stack.fiber.obj (LocallyDiscrete.mk (Opposite.op U)))

/-- A point of the orbicurve with a nontrivial automorphism: the necessary
condition for the orbicurve to have a stacky point. -/
def S1994HasNontrivialAut (X : Iut.HyperbolicOrbicurve F) : Prop :=
  ∃ (U : Iut.SchemeOverField F) (P : S1994Point X U)
    (f : CategoryTheory.End P), f ≠ 𝟙 P

/-- A point of the orbicurve whose automorphism has order n: a stacky point of
order n.  For n = l this is the l-tors point, for n = 2 the sign point. -/
def S1994HasAutOfOrder (X : Iut.HyperbolicOrbicurve F) (n : ℕ) : Prop :=
  ∃ (U : Iut.SchemeOverField F) (P : S1994Point X U)
    (f : CategoryTheory.End P), f ≠ 𝟙 P ∧ f ^ n = 𝟙 P

theorem S1994nontrivialAut_of_autOfOrder (X : Iut.HyperbolicOrbicurve F) {n : ℕ}
    (h : S1994HasAutOfOrder X n) : S1994HasNontrivialAut X := by
  obtain ⟨U, P, f, hf, -⟩ := h
  exact ⟨U, P, f, hf⟩

theorem S1994not_autOfOrder_of_not_nontrivial (X : Iut.HyperbolicOrbicurve F) {n : ℕ}
    (h : ¬ S1994HasNontrivialAut X) : ¬ S1994HasAutOfOrder X n :=
  fun hn => h (S1994nontrivialAut_of_autOfOrder X hn)

end Stacky

/-! ## 4. Representable orbicurves exist, and have no stacky points -/

section Representable

variable (F : Type u) [Field F]

/-- Every representable etale pseudofunctor is an etale stack: the
discrete-sheaf descent bridge of S1419, applied to the representable sheaf. -/
theorem S1994RepresentableIsStack (X : Iut.SchemeOverField F) :
    (Iut.schemeRepresentableEtalePseudofunctor F X).IsStack
      (Iut.SchemeOverField.etaleTopology F) := by
  have hP : Presieve.IsSheaf (Iut.SchemeOverField.etaleTopology F) (yoneda.obj X) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      (representableEtalePresheaf_isSheaf (F := F) X)
  change (discretePseudo (C := Iut.SchemeOverField F) (yoneda.obj X)).IsStack
    (Iut.SchemeOverField.etaleTopology F)
  exact DiscreteSheafStack.discretePseudo_isStack (P := yoneda.obj X) hP

/-- The actual hyperbolic orbicurve realised by a scheme over F, carrying an
arbitrary hyperbolic signature.  This is the orbicurve construction used
everywhere in the tree (S1419, S1726, S1886): the signature is stored on the
stack, it is not derived from the geometry. -/
noncomputable def S1994RepresentableOrbicurve (X : Iut.SchemeOverField F)
    (σ : Iut.OrbicurveSignature) (hσ : σ.IsHyperbolic) :
    Iut.HyperbolicOrbicurve F :=
  realizedHyperbolicOrbicurve F (Iut.schemeRepresentableEtalePseudofunctor F X)
    (S1994RepresentableIsStack F X) σ hσ

@[simp] theorem S1994RepresentableOrbicurve_signature (X : Iut.SchemeOverField F)
    (σ : Iut.OrbicurveSignature) (hσ : σ.IsHyperbolic) :
    (S1994RepresentableOrbicurve F X σ hσ).signature = σ := rfl

@[simp] theorem S1994RepresentableOrbicurve_stack_fiber (X : Iut.SchemeOverField F)
    (σ : Iut.OrbicurveSignature) (hσ : σ.IsHyperbolic) :
    (S1994RepresentableOrbicurve F X σ hσ).stack.fiber =
      Iut.schemeRepresentableEtalePseudofunctor F X := rfl

/-- Every automorphism of every point of a representable orbicurve is the
identity: its fibers are discrete categories. -/
theorem S1994RepresentableOrbicurve_aut_eq_id (X : Iut.SchemeOverField F)
    (σ : Iut.OrbicurveSignature) (hσ : σ.IsHyperbolic)
    (U : Iut.SchemeOverField F)
    (P : S1994Point (S1994RepresentableOrbicurve F X σ hσ) U)
    (f : CategoryTheory.End P) : f = 𝟙 P := by
  haveI : Subsingleton (CategoryTheory.End P) :=
    Discrete.instSubsingletonDiscreteHom P P
  exact Subsingleton.elim f (𝟙 P)

/-- A representable orbicurve has no point with a nontrivial automorphism. -/
theorem S1994RepresentableOrbicurve_noAut (X : Iut.SchemeOverField F)
    (σ : Iut.OrbicurveSignature) (hσ : σ.IsHyperbolic) :
    ¬ S1994HasNontrivialAut (S1994RepresentableOrbicurve F X σ hσ) := by
  intro h
  obtain ⟨U, P, f, hf⟩ := h
  exact hf (S1994RepresentableOrbicurve_aut_eq_id F X σ hσ U P f)

/-- Therefore it has no stacky point of any order: in particular not the
order-l point of the l-tors orbicurve. -/
theorem S1994RepresentableOrbicurve_noAutOfOrder (X : Iut.SchemeOverField F)
    (σ : Iut.OrbicurveSignature) (hσ : σ.IsHyperbolic) (n : ℕ) :
    ¬ S1994HasAutOfOrder (S1994RepresentableOrbicurve F X σ hσ) n :=
  S1994not_autOfOrder_of_not_nontrivial _
    (S1994RepresentableOrbicurve_noAut F X σ hσ)

end Representable

/-! ## 5. Labels are not geometry: the S1989 record is label-free -/

section Relabel

variable {F : Type u} [Field F]

/-- Relabel the stored signature of an etale stack, keeping its fiber and its
descent proof. -/
def S1994RelabelStack (S : Iut.EtaleStackOverField F)
    (σ : Iut.OrbicurveSignature) : Iut.EtaleStackOverField F :=
  { fiber := S.fiber, isStack := S.isStack, orbicurveSignature := some σ }

@[simp] theorem S1994RelabelStack_fiber (S : Iut.EtaleStackOverField F)
    (σ : Iut.OrbicurveSignature) :
    (S1994RelabelStack S σ).fiber = S.fiber := rfl

/-- Change the stored signature of an orbicurve, keeping its etale stack fiber
and its descent proof. -/
noncomputable def S1994Relabel (X : Iut.HyperbolicOrbicurve F)
    (σ : Iut.OrbicurveSignature) (hσ : σ.IsHyperbolic) :
    Iut.HyperbolicOrbicurve F where
  stack := S1994RelabelStack X.stack σ
  geometry :=
    { signature := σ
      realizes_signature := rfl
      hyperbolic := hσ }

@[simp] theorem S1994Relabel_signature (X : Iut.HyperbolicOrbicurve F)
    (σ : Iut.OrbicurveSignature) (hσ : σ.IsHyperbolic) :
    (S1994Relabel X σ hσ).signature = σ := rfl

@[simp] theorem S1994Relabel_stack_fiber (X : Iut.HyperbolicOrbicurve F)
    (σ : Iut.OrbicurveSignature) (hσ : σ.IsHyperbolic) :
    (S1994Relabel X σ hσ).stack.fiber = X.stack.fiber := rfl

/-- Relabelling keeps every morphism: a morphism of orbicurves only sees the
etale stack fiber. -/
def S1994RelabelHom {X Y : Iut.HyperbolicOrbicurve F}
    (σ τ : Iut.OrbicurveSignature) (hσ : σ.IsHyperbolic) (hτ : τ.IsHyperbolic)
    (f : X.Hom Y) : (S1994Relabel X σ hσ).Hom (S1994Relabel Y τ hτ) :=
  f

/-- Transport a base-change presentation along a relabelling of the source. -/
noncomputable def S1994TransportPresentationSource
    {source target : Iut.EtaleStackOverField F} (σ : Iut.OrbicurveSignature)
    (map : source.Hom target) (testScheme : Iut.SchemeOverField F)
    (point :
      Pseudofunctor.StrongTrans
        (Iut.schemeRepresentableEtalePseudofunctor F testScheme) target.fiber)
    (P : Iut.EtaleStackBaseChangePresentation map testScheme point) :
    @Iut.EtaleStackBaseChangePresentation F _ (S1994RelabelStack source σ) target
      map testScheme point where
  pullbackScheme := P.pullbackScheme
  projection := P.projection
  projectionMap := P.projectionMap
  toSource := P.toSource
  commutes := P.commutes
  isPullback := P.isPullback

/-- Transport a base-change presentation along relabellings of source and
target. -/
noncomputable def S1994TransportPresentation
    {source target : Iut.EtaleStackOverField F}
    (σ τ : Iut.OrbicurveSignature)
    (map : source.Hom target) (testScheme : Iut.SchemeOverField F)
    (point :
      Pseudofunctor.StrongTrans
        (Iut.schemeRepresentableEtalePseudofunctor F testScheme) target.fiber)
    (P : Iut.EtaleStackBaseChangePresentation map testScheme point) :
    @Iut.EtaleStackBaseChangePresentation F _
      (S1994RelabelStack source σ) (S1994RelabelStack target τ) map testScheme
      point where
  pullbackScheme := P.pullbackScheme
  projection := P.projection
  projectionMap := P.projectionMap
  toSource := P.toSource
  commutes := P.commutes
  isPullback := P.isPullback

/-- The finite-etale certificate transports along a relabelling of the
source. -/
noncomputable def S1994TransportFiniteEtaleSource
    {source target : Iut.EtaleStackOverField F} (σ : Iut.OrbicurveSignature)
    (map : source.Hom target)
    (hf : Iut.EtaleStackFiniteEtaleMorphism map) :
    @Iut.EtaleStackRepresentableMorphismProperty F _
      (fun f => AlgebraicGeometry.IsFinite f ∧ AlgebraicGeometry.Etale f)
      (S1994RelabelStack source σ) target map where
  baseChange testScheme point :=
    S1994TransportPresentationSource σ map testScheme point
      (hf.baseChange testScheme point)
  hasProperty testScheme point := hf.hasProperty testScheme point

/-- The finite-etale certificate transports along relabellings of source and
target. -/
noncomputable def S1994TransportFiniteEtale
    {source target : Iut.EtaleStackOverField F}
    (σ τ : Iut.OrbicurveSignature)
    (map : source.Hom target)
    (hf : Iut.EtaleStackFiniteEtaleMorphism map) :
    @Iut.EtaleStackRepresentableMorphismProperty F _
      (fun f => AlgebraicGeometry.IsFinite f ∧ AlgebraicGeometry.Etale f)
      (S1994RelabelStack source σ) (S1994RelabelStack target τ) map where
  baseChange testScheme point :=
    S1994TransportPresentation σ τ map testScheme point
      (hf.baseChange testScheme point)
  hasProperty testScheme point := hf.hasProperty testScheme point

/-- The degree predicate transports along a relabelling of the source. -/
theorem S1994TransportDegreeSource
    {X Y : Iut.HyperbolicOrbicurve F} (σ : Iut.OrbicurveSignature)
    (hσ : σ.IsHyperbolic) (map : X.Hom Y)
    (hf : Iut.EtaleStackFiniteEtaleMorphism map) (n : ℕ)
    (hd : StackFiniteEtaleDegree map hf n) :
    @StackFiniteEtaleDegree F _ (S1994Relabel X σ hσ) Y map
      (S1994TransportFiniteEtaleSource (source := X.stack) (target := Y.stack)
        σ map hf) n := by
  intro testScheme point t
  exact hd testScheme point t

/-- The degree predicate transports along relabellings of source and
target. -/
theorem S1994TransportDegree
    {X Y : Iut.HyperbolicOrbicurve F} (σ τ : Iut.OrbicurveSignature)
    (hσ : σ.IsHyperbolic) (hτ : τ.IsHyperbolic) (map : X.Hom Y)
    (hf : Iut.EtaleStackFiniteEtaleMorphism map) (n : ℕ)
    (hd : StackFiniteEtaleDegree map hf n) :
    @StackFiniteEtaleDegree F _ (S1994Relabel X σ hσ) (S1994Relabel Y τ hτ) map
      (S1994TransportFiniteEtale (source := X.stack) (target := Y.stack)
        σ τ map hf) n := by
  intro testScheme point t
  exact hd testScheme point t

end Relabel

/-! ### 5.1 The label-free K-side cover record -/

/-- The S1989 K-side cover record with the two signature fields deleted.  It
is the geometric content of the record. -/
structure KSideCoverUnlabelled (l : PrimeGeFive) (A : InitialThetaArithmeticData l)
    (S : SourceSignQuotientData A) (C : S1984PaperKCore l A S) where
  xArrow : Iut.HyperbolicOrbicurve A.K
  cArrow : Iut.HyperbolicOrbicurve A.K
  xArrow_to_xK : xArrow.Hom C.xK
  xArrow_to_xK_finiteEtale : Iut.EtaleStackFiniteEtaleMorphism xArrow_to_xK
  xArrow_to_xK_degree : StackFiniteEtaleDegree xArrow_to_xK xArrow_to_xK_finiteEtale l.value
  cArrow_to_cK : cArrow.Hom C.cK
  cArrow_to_cK_finiteEtale : Iut.EtaleStackFiniteEtaleMorphism cArrow_to_cK
  cArrow_to_cK_degree : StackFiniteEtaleDegree cArrow_to_cK cArrow_to_cK_finiteEtale l.value
  xArrow_to_cArrow : xArrow.Hom cArrow
  xArrow_to_cArrow_finiteEtale : Iut.EtaleStackFiniteEtaleMorphism xArrow_to_cArrow
  quotientSquare :
    Iut.HyperbolicOrbicurve.Hom.TwoIso
      (Iut.HyperbolicOrbicurve.Hom.comp xArrow_to_cArrow cArrow_to_cK)
      (Iut.HyperbolicOrbicurve.Hom.comp xArrow_to_xK C.coreQuotient)

namespace KSideCoverUnlabelled

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
variable {S : SourceSignQuotientData A} {C : S1984PaperKCore l A S}

/-- Forget the signature fields of the S1989 record. -/
def ofLabelled (K : KSideCoverActual l A S C) :
    KSideCoverUnlabelled l A S C where
  xArrow := K.xArrow
  cArrow := K.cArrow
  xArrow_to_xK := K.xArrow_to_xK
  xArrow_to_xK_finiteEtale := K.xArrow_to_xK_finiteEtale
  xArrow_to_xK_degree := K.xArrow_to_xK_degree
  cArrow_to_cK := K.cArrow_to_cK
  cArrow_to_cK_finiteEtale := K.cArrow_to_cK_finiteEtale
  cArrow_to_cK_degree := K.cArrow_to_cK_degree
  xArrow_to_cArrow := K.xArrow_to_cArrow
  xArrow_to_cArrow_finiteEtale := K.xArrow_to_cArrow_finiteEtale
  quotientSquare := K.quotientSquare

/-- Attach the paper signatures: relabelling changes no geometric field, so
every label-free record becomes a labelled S1989 record. -/
noncomputable def toLabelled (U : KSideCoverUnlabelled l A S C) :
    KSideCoverActual l A S C where
  xArrow := S1994Relabel U.xArrow (sourceTypeOneLTorsion l)
    (sourceTypeOneLTorsion_hyperbolic l)
  cArrow := S1994Relabel U.cArrow (sourceTypeOneLTorsionPlusMinus l)
    (sourceTypeOneLTorsionPlusMinus_hyperbolic l)
  xArrow_type := rfl
  cArrow_type := rfl
  xArrow_to_xK := U.xArrow_to_xK
  xArrow_to_xK_finiteEtale :=
    S1994TransportFiniteEtaleSource (source := U.xArrow.stack) (target := C.xK.stack)
      (sourceTypeOneLTorsion l) U.xArrow_to_xK U.xArrow_to_xK_finiteEtale
  xArrow_to_xK_degree :=
    S1994TransportDegreeSource (X := U.xArrow) (Y := C.xK) (sourceTypeOneLTorsion l)
      (sourceTypeOneLTorsion_hyperbolic l) U.xArrow_to_xK U.xArrow_to_xK_finiteEtale
      l.value U.xArrow_to_xK_degree
  cArrow_to_cK := U.cArrow_to_cK
  cArrow_to_cK_finiteEtale :=
    S1994TransportFiniteEtaleSource (source := U.cArrow.stack) (target := C.cK.stack)
      (sourceTypeOneLTorsionPlusMinus l) U.cArrow_to_cK U.cArrow_to_cK_finiteEtale
  cArrow_to_cK_degree :=
    S1994TransportDegreeSource (X := U.cArrow) (Y := C.cK)
      (sourceTypeOneLTorsionPlusMinus l) (sourceTypeOneLTorsionPlusMinus_hyperbolic l)
      U.cArrow_to_cK U.cArrow_to_cK_finiteEtale l.value U.cArrow_to_cK_degree
  xArrow_to_cArrow := U.xArrow_to_cArrow
  xArrow_to_cArrow_finiteEtale :=
    S1994TransportFiniteEtale (source := U.xArrow.stack) (target := U.cArrow.stack)
      (sourceTypeOneLTorsion l) (sourceTypeOneLTorsionPlusMinus l)
      U.xArrow_to_cArrow U.xArrow_to_cArrow_finiteEtale
  quotientSquare := U.quotientSquare

end KSideCoverUnlabelled

/-- The S1989 record and its label-free form are nonempty together: the two
signature fields carry no geometric content. -/
theorem S1994KSideCoverActual_iff_unlabelled
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    {S : SourceSignQuotientData A} {C : S1984PaperKCore l A S} :
    Nonempty (KSideCoverActual l A S C) ↔
      Nonempty (KSideCoverUnlabelled l A S C) := by
  constructor
  · rintro ⟨K⟩
    exact ⟨KSideCoverUnlabelled.ofLabelled K⟩
  · rintro ⟨U⟩
    exact ⟨KSideCoverUnlabelled.toLabelled U⟩

/-- The sharp form of label vacuity: the labelled S1989 record is produced by
*arbitrary* orbicurves over K, arbitrary finite-etale degree-l maps to the two
cores and an arbitrary 2-commutative square.  The record therefore carries no
l-tors geometry; it is exactly its label-free form. -/
theorem S1994labelledRecord_of_arbitrary_endpoints
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    {S : SourceSignQuotientData A} {C : S1984PaperKCore l A S}
    (X Y : Iut.HyperbolicOrbicurve A.K)
    (f : X.Hom C.xK) (hf : Iut.EtaleStackFiniteEtaleMorphism f)
    (df : StackFiniteEtaleDegree f hf l.value)
    (g : Y.Hom C.cK) (hg : Iut.EtaleStackFiniteEtaleMorphism g)
    (dg : StackFiniteEtaleDegree g hg l.value)
    (q : X.Hom Y) (hq : Iut.EtaleStackFiniteEtaleMorphism q)
    (square :
      Iut.HyperbolicOrbicurve.Hom.TwoIso
        (Iut.HyperbolicOrbicurve.Hom.comp q g)
        (Iut.HyperbolicOrbicurve.Hom.comp f C.coreQuotient)) :
    Nonempty (KSideCoverActual l A S C) := by
  refine ⟨KSideCoverUnlabelled.toLabelled
    { xArrow := X
      cArrow := Y
      xArrow_to_xK := f
      xArrow_to_xK_finiteEtale := hf
      xArrow_to_xK_degree := df
      cArrow_to_cK := g
      cArrow_to_cK_finiteEtale := hg
      cArrow_to_cK_degree := dg
      xArrow_to_cArrow := q
      xArrow_to_cArrow_finiteEtale := hq
      quotientSquare := square }⟩

/-! ## 6. The paper-faithful cover datum and the exact first missing -/

/-- The paper's K-side cover datum: the S1989 record together with the honest
stacky-point geometry of the l-tors orbicurve.  X_K^-> has a point with an
automorphism of order l; C_K^-> has the order-2 sign point and the order-l
l-tors point. -/
structure S1994PaperKSideCover (l : PrimeGeFive) (A : InitialThetaArithmeticData l)
    (S : SourceSignQuotientData A) (C : S1984PaperKCore l A S) where
  cover : KSideCoverActual l A S C
  xArrow_order_l : S1994HasAutOfOrder (F := A.K) cover.xArrow l.value
  cArrow_order_two : S1994HasAutOfOrder (F := A.K) cover.cArrow 2
  cArrow_order_l : S1994HasAutOfOrder (F := A.K) cover.cArrow l.value

/-- The paper-faithful K-side cover is missing: no inhabitant is constructed. -/
def S1994PaperKSideCoverMissing (l : PrimeGeFive) (A : InitialThetaArithmeticData l)
    (S : SourceSignQuotientData A) (C : S1984PaperKCore l A S) : Prop :=
  Nonempty (S1994PaperKSideCover l A S C)

namespace S1994PaperKSideCover

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
variable {S : SourceSignQuotientData A} {C : S1984PaperKCore l A S}

/-- The paper datum refines the S1989 record. -/
theorem toKSideCoverMissing (P : S1994PaperKSideCover l A S C) :
    KSideCoverMissing l A S C :=
  ⟨P.cover⟩

/-- The paper datum refines the label-free record as well. -/
theorem toUnlabelled (P : S1994PaperKSideCover l A S C) :
    Nonempty (KSideCoverUnlabelled l A S C) :=
  ⟨KSideCoverUnlabelled.ofLabelled P.cover⟩

/-- The paper datum forces an actual orbicurve over K with an order-l stacky
point. -/
theorem stackyOrbicurve (P : S1994PaperKSideCover l A S C) :
    ∃ X : Iut.HyperbolicOrbicurve A.K, S1994HasAutOfOrder (F := A.K) X l.value :=
  ⟨P.cover.xArrow, P.xArrow_order_l⟩

/-- Its X_K^-> is not any representable orbicurve. -/
theorem xArrow_not_representable (P : S1994PaperKSideCover l A S C)
    (X : Iut.SchemeOverField A.K) (σ : Iut.OrbicurveSignature) (hσ : σ.IsHyperbolic)
    (hx : P.cover.xArrow = S1994RepresentableOrbicurve (F := A.K) X σ hσ) : False := by
  have hstacky : S1994HasAutOfOrder (F := A.K)
      (S1994RepresentableOrbicurve (F := A.K) X σ hσ) l.value := hx ▸ P.xArrow_order_l
  exact S1994RepresentableOrbicurve_noAutOfOrder (F := A.K) X σ hσ l.value hstacky

end S1994PaperKSideCover

/-- The exact first missing at the geometric level: an actual orbicurve over
A.K with a point whose automorphism has order l.  Equivalently an actual
non-representable etale stack over A.K (the l-tors root stack). -/
def S1994StackyOrbicurveMissing (l : PrimeGeFive) (A : InitialThetaArithmeticData l) :
    Prop :=
  ∃ X : Iut.HyperbolicOrbicurve A.K, S1994HasAutOfOrder (F := A.K) X l.value

theorem S1994stackyOrbicurveMissing_of_paper
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    {S : SourceSignQuotientData A} {C : S1984PaperKCore l A S}
    (h : S1994PaperKSideCoverMissing l A S C) :
    S1994StackyOrbicurveMissing l A := by
  obtain ⟨P⟩ := h
  exact P.stackyOrbicurve

/-- The paper cover is exactly the S1989 record plus the three stacky-point
conditions: no further geometric content is hidden. -/
theorem S1994paperKSideCoverMissing_iff
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    {S : SourceSignQuotientData A} {C : S1984PaperKCore l A S} :
    S1994PaperKSideCoverMissing l A S C ↔
      ∃ K : KSideCoverActual l A S C,
        S1994HasAutOfOrder (F := A.K) K.xArrow l.value ∧
          S1994HasAutOfOrder (F := A.K) K.cArrow 2 ∧
            S1994HasAutOfOrder (F := A.K) K.cArrow l.value := by
  constructor
  · rintro ⟨P⟩
    exact ⟨P.cover, P.xArrow_order_l, P.cArrow_order_two, P.cArrow_order_l⟩
  · rintro ⟨K, hx, htwo, hl⟩
    exact ⟨{ cover := K, xArrow_order_l := hx, cArrow_order_two := htwo, cArrow_order_l := hl }⟩

/-! ## 7. The label-only orbicurve: the paper label does not give the geometry -/

section LabelOnly

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData l}

/-- The base scheme Spec K, as a scheme over K. -/
noncomputable def S1994BaseScheme (A : InitialThetaArithmeticData l) :
    Iut.SchemeOverField A.K :=
  Over.mk (𝟙 (Spec (CommRingCat.of A.K)))

/-- An actual orbicurve over A.K carrying the paper's (1,l-tors) label, built
as the representable stack of Spec K.  It exists; it is not the l-tors
orbifold. -/
noncomputable def S1994LabelOnlyLTorsOrbicurve (l : PrimeGeFive)
    (A : InitialThetaArithmeticData l) : Iut.HyperbolicOrbicurve A.K :=
  S1994RepresentableOrbicurve (F := A.K) (S1994BaseScheme A)
    (sourceTypeOneLTorsion l) (sourceTypeOneLTorsion_hyperbolic l)

@[simp] theorem S1994LabelOnlyLTorsOrbicurve_signature (l : PrimeGeFive)
    (A : InitialThetaArithmeticData l) :
    (S1994LabelOnlyLTorsOrbicurve l A).signature = sourceTypeOneLTorsion l := rfl

/-- The label-only orbicurve has no nontrivial automorphisms at any point. -/
theorem S1994LabelOnlyLTorsOrbicurve_noAut (l : PrimeGeFive)
    (A : InitialThetaArithmeticData l) :
    ¬ S1994HasNontrivialAut (S1994LabelOnlyLTorsOrbicurve l A) :=
  S1994RepresentableOrbicurve_noAut (F := A.K) (S1994BaseScheme A)
    (sourceTypeOneLTorsion l) (sourceTypeOneLTorsion_hyperbolic l)

/-- In particular it is not the paper's l-tors orbicurve: it has no stacky
point of order l, although it carries the (1,l-tors) signature.  Hence the
S1989 signature fields do not encode the l-tors geometry. -/
theorem S1994LabelOnlyLTorsOrbicurve_noAutOfOrder (l : PrimeGeFive)
    (A : InitialThetaArithmeticData l) (n : ℕ) :
    ¬ S1994HasAutOfOrder (S1994LabelOnlyLTorsOrbicurve l A) n :=
  S1994RepresentableOrbicurve_noAutOfOrder (F := A.K) (S1994BaseScheme A)
    (sourceTypeOneLTorsion l) (sourceTypeOneLTorsion_hyperbolic l) n

/-- The label and the geometry are independent: an orbicurve with the exact
(1,l-tors) label exists, and an orbicurve with an order-l stacky point is
missing.  These are different obligations. -/
theorem S1994label_does_not_force_stackiness :
    (∃ X : Iut.HyperbolicOrbicurve A.K, X.signature = sourceTypeOneLTorsion l) ∧
      ¬ S1994HasAutOfOrder (S1994LabelOnlyLTorsOrbicurve l A) l.value :=
  ⟨⟨S1994LabelOnlyLTorsOrbicurve l A, rfl⟩,
    S1994LabelOnlyLTorsOrbicurve_noAutOfOrder l A l.value⟩

end LabelOnly

/-! ## 8. Summary: the exact first missing, and its decomposition -/

/-- The target of this package: the paper-faithful K-side cover over the
production core. -/
def S1994FirstMissing (l : PrimeGeFive) (A : InitialThetaArithmeticData l)
    (S : SourceSignQuotientData A)
    {C : SourceClauseA A S} {B : SourceClauseB A S C}
    {Dc : SourceClauseC A S C B}
    (E : SourceClauseD A S C B Dc) : Prop :=
  S1994PaperKSideCoverMissing l A S (S1984PaperKCore.ofSource E)

/-- The first missing implies the S1989 cover record over the production
core. -/
theorem S1994firstMissing_implies_record
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    {S : SourceSignQuotientData A}
    {C : SourceClauseA A S} {B : SourceClauseB A S C}
    {Dc : SourceClauseC A S C B}
    (E : SourceClauseD A S C B Dc) :
    S1994FirstMissing l A S E → KSideCoverMissing l A S (S1984PaperKCore.ofSource E) := by
  intro h
  exact S1994PaperKSideCover.toKSideCoverMissing h.some

/-- The first missing decomposes exactly into the S1989 record plus the three
stacky-point conditions over the production core. -/
theorem S1994firstMissing_iff
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    {S : SourceSignQuotientData A}
    {C : SourceClauseA A S} {B : SourceClauseB A S C}
    {Dc : SourceClauseC A S C B}
    (E : SourceClauseD A S C B Dc) :
    S1994FirstMissing l A S E ↔
      ∃ K : KSideCoverActual l A S (S1984PaperKCore.ofSource E),
        S1994HasAutOfOrder (F := A.K) K.xArrow l.value ∧
          S1994HasAutOfOrder (F := A.K) K.cArrow 2 ∧
            S1994HasAutOfOrder (F := A.K) K.cArrow l.value :=
  S1994paperKSideCoverMissing_iff

/-- The first missing forces an actual orbicurve over K with an order-l stacky
point: this is the curve-geometry half that the record does not carry. -/
theorem S1994firstMissing_implies_stacky
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    {S : SourceSignQuotientData A}
    {C : SourceClauseA A S} {B : SourceClauseB A S C}
    {Dc : SourceClauseC A S C B}
    (E : SourceClauseD A S C B Dc) :
    S1994FirstMissing l A S E → S1994StackyOrbicurveMissing l A :=
  S1994stackyOrbicurveMissing_of_paper

/-- The package's consumer entry point over the production core: the paper
K-side cover forces an actual orbicurve over K with an order-l stacky point,
and the S1989 cover record over the production core is equivalent to its
label-free form.  Hence the residual obligation is a non-representable l-tors
orbifold over A.K together with its finite-etale degree-l stack maps to the
two K-cores. -/
theorem S1994production_conclusion
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    {S : SourceSignQuotientData A}
    {C : SourceClauseA A S} {B : SourceClauseB A S C}
    {Dc : SourceClauseC A S C B}
    (E : SourceClauseD A S C B Dc) :
    (S1994FirstMissing l A S E → S1994StackyOrbicurveMissing l A) ∧
      (Nonempty (KSideCoverActual l A S (S1984PaperKCore.ofSource E)) ↔
        Nonempty (KSideCoverUnlabelled l A S (S1984PaperKCore.ofSource E))) :=
  ⟨S1994firstMissing_implies_stacky E, S1994KSideCoverActual_iff_unlabelled⟩

/-- The obstruction part of the package in one statement: a representable
orbicurve has no nontrivial automorphism at any point, hence no stacky point of
any order.  Applied to the paper's l-tors orbicurve, this rules out the only
immediate realisation route. -/
theorem S1994representable_no_stacky_summary (l : PrimeGeFive)
    (A : InitialThetaArithmeticData l)
    (X : Iut.SchemeOverField A.K) (σ : Iut.OrbicurveSignature) (hσ : σ.IsHyperbolic)
    (n : ℕ) :
    (¬ S1994HasNontrivialAut (S1994RepresentableOrbicurve (F := A.K) X σ hσ)) ∧
      (¬ S1994HasAutOfOrder (S1994RepresentableOrbicurve (F := A.K) X σ hσ) n) :=
  ⟨S1994RepresentableOrbicurve_noAut (F := A.K) X σ hσ,
    S1994RepresentableOrbicurve_noAutOfOrder (F := A.K) X σ hσ n⟩

end LeanFormal.IUT.XiFPaper.S1994KSideCovers

/-! ## 9. Axiom footprint -/

#print axioms LeanFormal.IUT.XiFPaper.S1994KSideCovers.S1994KernelLine_card
#print axioms LeanFormal.IUT.XiFPaper.S1994KSideCovers.S1994KernelLine_line
#print axioms LeanFormal.IUT.XiFPaper.S1994KSideCovers.S1994KernelVector_ne_zero
#print axioms LeanFormal.IUT.XiFPaper.S1994KSideCovers.S1994rankOneQuotient_distinguished
#print axioms LeanFormal.IUT.XiFPaper.S1994KSideCovers.S1994IsogenyKernelDatumOfClauseC
#print axioms LeanFormal.IUT.XiFPaper.S1994KSideCovers.S1994RepresentableIsStack
#print axioms LeanFormal.IUT.XiFPaper.S1994KSideCovers.S1994RepresentableOrbicurve_noAut
#print axioms LeanFormal.IUT.XiFPaper.S1994KSideCovers.S1994RepresentableOrbicurve_noAutOfOrder
#print axioms LeanFormal.IUT.XiFPaper.S1994KSideCovers.S1994KSideCoverActual_iff_unlabelled
#print axioms LeanFormal.IUT.XiFPaper.S1994KSideCovers.S1994labelledRecord_of_arbitrary_endpoints
#print axioms LeanFormal.IUT.XiFPaper.S1994KSideCovers.S1994paperKSideCoverMissing_iff
#print axioms LeanFormal.IUT.XiFPaper.S1994KSideCovers.S1994firstMissing_iff
#print axioms LeanFormal.IUT.XiFPaper.S1994KSideCovers.S1994firstMissing_implies_stacky
#print axioms LeanFormal.IUT.XiFPaper.S1994KSideCovers.S1994PaperKSideCover.xArrow_not_representable
#print axioms LeanFormal.IUT.XiFPaper.S1994KSideCovers.S1994label_does_not_force_stackiness
#print axioms LeanFormal.IUT.XiFPaper.S1994KSideCovers.S1994production_conclusion
#print axioms LeanFormal.IUT.XiFPaper.S1994KSideCovers.S1994representable_no_stacky_summary
