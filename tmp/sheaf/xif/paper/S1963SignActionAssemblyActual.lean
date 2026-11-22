import tmp.sheaf.xif.paper.S1932SignActionQuotientActual

/-!
# S1963: the coherent sign action of the actual S1726 orbicurve

S1932 reduced the first missing datum of the paper-faithful orbicurve
construction to

  S1932SignActionMissing l :
    exists A : OrbicurveSignAction S1726Orbicurve,
      A.inversion = S1898EllipticInvolution l.

The geometric input is already complete: S1898 constructs the actual 2-Yoneda
lift of the affine [-1] endomorphism, and S1932 constructs its square

  S1932SigmaSqIso : Sigma ; Sigma ~= 1.

This file supplies the remaining bicategorical assembly: the pseudofunctor
from the one-object sign-group bicategory to etale stack pseudofunctors.  On
the nontrivial group element it is Sigma; on the identity it is the identity
strong transformation.  The only nontrivial mapComp component is
S1932SigmaSqIso; the other three are the left/right unitors of vertical
composition of strong transformations.  Coherence is automatic because every
2-cell between endomorphisms of the representable S1726 stack is a
subsingleton (S1932StrongTransSubsingleton).

The unitors are packaged as named definitions S1963LeftUnitor and
S1963RightUnitor, following S1932's hint; the lambda/rho notation is not used
for strong transformations.  No action field is postulated: the inversion is
the actual S1898EllipticInvolutionHom, the square coherence is the actual
S1932SigmaSqIso, and the base equivalence is the identity equivalence.

## Result

S1963SignActionMissing proves S1932SignActionMissing l for every prime
l >= 5, by an actual OrbicurveSignAction whose inversion is
S1898EllipticInvolution l.  The quotient C_F = X_F/{+-1} and its universal
property remain outside this file; nothing here postulates them.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1963SignActionAssemblyActual

open CategoryTheory
open CategoryTheory.Bicategory
open AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1881D9D7bActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1732SourceAssemblyActual
open LeanFormal.IUT.XiFPaper.S1886D9OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1898EllipticInvolutionActual
open LeanFormal.IUT.XiFPaper.S1932SignActionQuotientActual

/-! ## 1. The sign group and its two values -/

/-- The sign group, regarded as a type of morphisms of the one-object index
groupoid. -/
abbrev S1963SignGroup := SignGroup

/-- The actual elliptic involution, as a strong transformation. -/
abbrev S1963Sigma : Pseudofunctor.StrongTrans S1898Stack S1898Stack :=
  S1932Sigma

/-- The unique object of the one-object sign-group category. -/
abbrev S1963SignIndex := SignActionIndex

/-- Extract the group element underlying a morphism of the sign index.  The
named wrapper avoids relying on the reducible identification of the hom-type
of SingleObj with the group during multiplication. -/
def S1963SignGroupOf {a b : S1963SignIndex} (f : a ⟶ b) : S1963SignGroup :=
  f.as

/-- Composition in the one-object category is multiplication with the two
arguments reversed. -/
theorem S1963SignGroupOf_comp {a b c : S1963SignIndex}
    (f : a ⟶ b) (g : b ⟶ c) :
    S1963SignGroupOf (f ≫ g) =
      S1963SignGroupOf g * S1963SignGroupOf f := rfl

/-- The nontrivial element of the sign group is not the identity. -/
theorem S1963SignGroup_generator_ne :
    (Multiplicative.ofAdd (1 : ZMod 2) : S1963SignGroup) ≠ 1 := by
  decide

/-- Every element of the sign group has square one. -/
theorem S1963SignGroup_mul_self (x : S1963SignGroup) : x * x = 1 := by
  revert x
  decide

/-- The product of two nontrivial elements of the sign group is the identity. -/
theorem S1963SignGroup_mul_eq_one {x y : S1963SignGroup}
    (hx : x ≠ 1) (hy : y ≠ 1) : x * y = 1 := by
  revert x y
  decide

/-! ## 2. Named unitors for strong transformations -/

/-- Left unitor for vertical composition of strong transformations, exposed
without the scoped lambda notation. -/
noncomputable def S1963LeftUnitor {X Y : EtaleStackPseudofunctor S1726K}
    (f : Pseudofunctor.StrongTrans X Y) :
    Iso (Pseudofunctor.StrongTrans.vcomp
      (Pseudofunctor.StrongTrans.id X) f) f := by
  letI : Bicategory (EtaleStackPseudofunctor S1726K) := inferInstance
  exact @Bicategory.leftUnitor (EtaleStackPseudofunctor S1726K) _ X Y f

/-- Right unitor for vertical composition of strong transformations, exposed
without the scoped rho notation. -/
noncomputable def S1963RightUnitor {X Y : EtaleStackPseudofunctor S1726K}
    (f : Pseudofunctor.StrongTrans X Y) :
    Iso (Pseudofunctor.StrongTrans.vcomp
      f (Pseudofunctor.StrongTrans.id Y)) f := by
  letI : Bicategory (EtaleStackPseudofunctor S1726K) := inferInstance
  exact @Bicategory.rightUnitor (EtaleStackPseudofunctor S1726K) _ X Y f

/-! ## 3. The value of the diagram on group elements -/

/-- The value of the sign diagram on a group element: the identity on 1 and
the actual elliptic involution on the nontrivial element. -/
noncomputable def S1963SigMapOf (x : S1963SignGroup) :
    Pseudofunctor.StrongTrans S1898Stack S1898Stack :=
  if h : x = 1 then Pseudofunctor.StrongTrans.id S1898Stack else S1963Sigma

theorem S1963SigMapOf_one :
    S1963SigMapOf 1 = Pseudofunctor.StrongTrans.id S1898Stack := by
  simp [S1963SigMapOf]

theorem S1963SigMapOf_ne {x : S1963SignGroup} (h : x ≠ 1) :
    S1963SigMapOf x = S1963Sigma := by
  simp [S1963SigMapOf, h]

/-- The mapComp component on composable group elements.  The four cases are
the two trivial unitors and the actual square Sigma ; Sigma ~= 1; the
identity/identity case is also a unitor. -/
noncomputable def S1963SigMapCompOf (x y : S1963SignGroup) :
    Iso (S1963SigMapOf (y * x))
      (Pseudofunctor.StrongTrans.vcomp
        (S1963SigMapOf x) (S1963SigMapOf y)) := by
  by_cases hx : x = 1
  · subst x
    simpa [S1963SigMapOf_one] using
      (S1963LeftUnitor (S1963SigMapOf y)).symm
  · by_cases hy : y = 1
    · subst y
      simpa [S1963SigMapOf_one] using
        (S1963RightUnitor (S1963SigMapOf x)).symm
    · have hxy : y * x = 1 := S1963SignGroup_mul_eq_one hy hx
      rw [hxy, S1963SigMapOf_one, S1963SigMapOf_ne hx, S1963SigMapOf_ne hy]
      exact S1932SigmaSqIso.symm

/-! ## 4. The pseudofunctor of the sign action -/

/-- The pseudofunctor of the sign action on the actual S1726 stack.  It is
the constant diagram with value S1898Stack, the identity strong
transformation on the group identity, the actual involution S1963Sigma on
the generator, and the actual square coherence.  The remaining coherence
equations are subsingleton eliminations. -/
noncomputable def S1963Diagram :
    SignActionIndex ⥤ᵖ EtaleStackPseudofunctor S1726K :=
  LocallyDiscrete.mkPseudofunctor
    (obj := fun _ => S1898Stack)
    (map := fun {b b'} f => S1963SigMapOf f)
    (mapId := fun b => eqToIso (by
      change S1963SigMapOf (1 : S1963SignGroup) =
        Pseudofunctor.StrongTrans.id S1898Stack
      exact S1963SigMapOf_one))
    (mapComp := fun {b₀ b₁ b₂} f g => S1963SigMapCompOf f g)
    (map₂_associator := fun f g h =>
      (S1932StrongTransSubsingleton _ _).elim _ _)
    (map₂_left_unitor := fun f =>
      (S1932StrongTransSubsingleton _ _).elim _ _)
    (map₂_right_unitor := fun f =>
      (S1932StrongTransSubsingleton _ _).elim _ _)

theorem S1963Diagram_obj :
    S1963Diagram.obj signActionObject = S1898Stack := rfl

theorem S1963Diagram_map_generator :
    S1963Diagram.map signActionGenerator = S1963Sigma := by
  change S1963SigMapOf (S1963SignGroupOf signActionGenerator) = S1963Sigma
  apply S1963SigMapOf_ne
  change (Multiplicative.ofAdd (1 : ZMod 2) : S1963SignGroup) ≠ 1
  exact S1963SignGroup_generator_ne

/-! ## 5. The actual sign action and the missing proposition -/

/-- The coherent sign action on the actual S1726 orbicurve.  Its base
equivalence is the identity equivalence, its inversion is the actual elliptic
involution, and its generator identification is the unitor comparison
(1 ; Sigma) ; 1 ~= Sigma. -/
noncomputable def S1963SignAction (l : PrimeGeFive) :
    Iut.OrbicurveSignAction S1726Orbicurve where
  diagram := S1963Diagram
  atBase := Bicategory.Equivalence.id S1898Stack
  inversion := S1963Sigma
  generator_identification := by
    rw [S1963Diagram_map_generator]
    show Iso (Pseudofunctor.StrongTrans.vcomp
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.id S1898Stack) S1963Sigma)
      (Pseudofunctor.StrongTrans.id S1898Stack)) S1963Sigma
    exact (S1963RightUnitor (Pseudofunctor.StrongTrans.vcomp
      (Pseudofunctor.StrongTrans.id S1898Stack) S1963Sigma)).trans
        (S1963LeftUnitor S1963Sigma)
  inversionSquared := S1932SigmaSqIso

/-- The inversion of the constructed action is the actual elliptic involution
of S1898, definitionally. -/
theorem S1963SignAction_inversion (l : PrimeGeFive) :
    (S1963SignAction l).inversion = S1898EllipticInvolution l := rfl

/-- The chosen generator of the sign action acts by the actual elliptic
involution. -/
theorem S1963SignAction_generator (l : PrimeGeFive) :
    (S1963SignAction l).diagram.map signActionGenerator = S1963Sigma :=
  S1963Diagram_map_generator

/-- S1932's exact missing proposition is proved.  The witness is the actual
coherent sign action constructed above; no action field is postulated. -/
theorem S1963SignActionMissing (l : PrimeGeFive) :
    S1932SignActionMissing l :=
  ⟨S1963SignAction l, S1963SignAction_inversion l⟩

/-- The S1898 packaging, now filled by the actual action. -/
noncomputable def S1963SignActionPackaging (l : PrimeGeFive) :
    S1898SignActionPackaging l where
  action := S1963SignAction l
  inversion_eq := S1963SignAction_inversion l

theorem S1963SignActionPackaging_nonempty (l : PrimeGeFive) :
    Nonempty (S1898SignActionPackaging l) :=
  ⟨S1963SignActionPackaging l⟩

/-! ## 6. Axiom footprint -/

#print axioms S1963SignGroup_generator_ne
#print axioms S1963SignGroup_mul_eq_one
#print axioms S1963LeftUnitor
#print axioms S1963RightUnitor
#print axioms S1963SigMapCompOf
#print axioms S1963Diagram
#print axioms S1963SignAction
#print axioms S1963SignActionMissing
#print axioms S1963SignActionPackaging

end LeanFormal.IUT.XiFPaper.S1963SignActionAssemblyActual

end
