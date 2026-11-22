/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors / S1851

# S1851: the assembly of field 5 -- base change R' -> Omega preserves finite group quotients

S1835 reduced the fifth field of the six-field geometric fibre functor at the closed
point (0,0) to the single statement

  S1835BCPreservesQuotients :
    forall (G : Type) [Group G] [Finite G],
      PreservesColimitsOfShape (SingleObj G) (S1835BC).op,

and S1847 proved its whole mathematical content: for every finite group `G` and every
finite etale `R'`-algebra `A` carrying a `G`-action, the canonical map

  Omega (x)_{R'} A^G  ->  (Omega (x)_{R'} A)^G

is an isomorphism (`fixedPointsBaseChange`, and its packaged form `fpbc` together with
`fpbc_tmul` on pure tensors).

This file performs the remaining, purely categorical, *elaboration* work:

1. `conePointAlgEquiv`: the comparison of the two candidate points of the limit cone.
   Rather than transporting S1847's `fpbc` (whose domain is `Omega (x) A^G` and whose
   codomain is the fixed-point subalgebra of the *tensor-product* action) across the
   subalgebra identity `fps_bc_eq_tensor`, we use the tensor-action presentation
   directly (S1847 suggestion (a)/(b)): the underlying algebra map of
   `fixedPointsBaseChange` is *definitionally* the tensor-product inclusion
   `Algebra.TensorProduct.map (AlgHom.id Omega Omega) A^G.val`.  Consequently the value
   of the point comparison on every element is `rfl`
   (`conePointAlgEquiv_val`), which is exactly the elementwise form that the naturality
   of the cone comparison needs.  (This is the same content as S1847's `fpbc_apply`,
   obtained without an induction by choosing the presentation adapted to the cone.)

2. `conePointIso`, `coneIso`: the isomorphism of cones

     invariantsCone (K >>> S1835BC)  ~=  S1835BC.mapCone (invariantsCone K)

   over the base-changed diagram `K >>> S1835BC`.  Its naturality is `coneIso_naturality`,
   which after extensionality is precisely `conePointAlgEquiv_val`.

3. `isLimitMapCone`: `IsLimit (S1835BC.mapCone (invariantsCone K))`, obtained from
   `S1830G2.invariantsIsLimit (K >>> S1835BC)` by `IsLimit.ofIsoLimit`.

4. `preservesLimitsOfShape_op_singleObj` :
   `PreservesLimitsOfShape (SingleObj G)^op S1835BC`, obtained from (3) and the
   uniqueness of limit cones (`IsLimit.uniqueUpToIso`).

5. `preservesColimitsOfShape_singleObj` :
   `PreservesColimitsOfShape (SingleObj G) (S1835BC).op`, by
   `preservesColimitsOfShape_op`.

6. `S1835BCPreservesQuotients_actual : S1835BCPreservesQuotients`, i.e. field 5 exactly
   as stated in S1835 (for `[Group G] [Finite G]`, with the `Fintype`/`DecidableEq`
   instances supplied internally by `Fintype.ofFinite` and `Classical.decEq`), and
   `S1851PreservesQuotients`: field 5 for the actual geometric fibre functor
   `S1835Fiber`, via `S1835PreservesQuotients_of`.

## Honest boundary

No sorry, admit, new axiom, Shrink, ULift or PUnit occurs in this file.  Every
declaration depends only on `propext`, `Classical.choice` and `Quot.sound` (axiom audit at
the end).  The target statement is not weakened: `S1835BCPreservesQuotients` is quoted
verbatim from S1835.
-/

import tmp.sheaf.xif.paper.S1847RPrimeQuotientsActual
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.CategoryTheory.Limits.Shapes.SingleObj

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.defProp false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual
open LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual.S1779FiniteEtaleClosure
open LeanFormal.IUT.XiFPaper.S1830G2G3RPrimeActual
open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
open LeanFormal.IUT.Foundations.AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S1835FiberRPrimeActual
open LeanFormal.IUT.XiFPaper.S1847RPrimeQuotientsActual

namespace LeanFormal.IUT.XiFPaper.S1851RPrimeQuotientsCompleteActual

attribute [local instance] S1779PointClosureAlgebra

variable {G : Type} [Group G] [Fintype G] [DecidableEq G]

section Main

variable (K : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{0} S1779R)

/-- The finite etale R'-algebra underlying the action diagram. -/
abbrev AK : Type := S1830G2.actionAlgebra K

/-- Its base change to Omega, with the action induced by the base-changed diagram. -/
abbrev AKbc : Type := S1830G2.actionAlgebra (K ⋙ S1835BC)

/-- The fixed points A^G of the acted-on algebra. -/
abbrev invK : Subalgebra S1779R (AK (G := G) K) :=
  fixedPointSubalgebra S1779R (AK (G := G) K) G

/-- The fixed points of the base change, for the action induced by the base-changed
diagram K >>> S1835BC. -/
abbrev invBC : Subalgebra S1835Omega (AKbc (G := G) K) :=
  fixedPointSubalgebra S1835Omega (AKbc (G := G) K) G

/-! ## 1. The comparison of the points of the two cones -/

/-- The canonical comparison Omega (x)_{R'} A^G -> (Omega (x)_{R'} A)^G, presented on
the tensor-product action (S1847 suggestion (a)): its underlying algebra map is
definitionally the tensor product of the identity with the inclusion A^G -> A. -/
noncomputable def conePointAlgEquiv :
    S1835Omega ⊗[S1779R] ↥(invK (G := G) K) ≃ₐ[S1835Omega] ↥(invBC (G := G) K) :=
  (fixedPointsBaseChange (R := S1779R) (T := S1835Omega) (A := AK (G := G) K) (G := G)
      (instT := TensorEqualizerFixedPoints.tensorMulSemiringAction S1779R (AK (G := G) K) G S1835Omega)
      (instC := TensorEqualizerFixedPoints.tensorSMulCommClass S1779R (AK (G := G) K) G S1835Omega)
      (fun g t a => TensorEqualizerFixedPoints.tensor_smul_tmul (R := S1779R) (A := AK (G := G) K)
        (G := G) (T := S1835Omega) (g := g) (t := t) (a := a))
      (isUnit_card_R' (G := G))).trans
    (Subalgebra.equivOfEq _ _ (fps_bc_eq_tensor K))

/-- The point comparison is the tensor inclusion on elements.  This is the elementwise
form needed for the naturality of the cone comparison; it holds definitionally because the
underlying algebra map of fixedPointsBaseChange is phiHom. -/
lemma conePointAlgEquiv_val (x : S1835Omega ⊗[S1779R] ↥(invK (G := G) K)) :
    fixedPointInclusion S1835Omega (AKbc (G := G) K) G (conePointAlgEquiv K x) =
      (S1835BC.map ((S1830G2.invariantsCone K).π.app (Opposite.op (SingleObj.star G)))).hom.hom x :=
  rfl

/-- The point of the limit cone over K >>> S1835BC is the base change of the point of the
limit cone over K. -/
noncomputable def conePointIso :
    S1835BC.obj (S1830G2.invariantsObject K) ≅ S1830G2.invariantsObject (K ⋙ S1835BC) :=
  CommAlgCat.FiniteEtale.isoMk (conePointAlgEquiv K)

/-! ## 2. The comparison of the two cones -/

/-- Naturality of the cone comparison.  After extensionality this is
conePointAlgEquiv_val. -/
lemma coneIso_naturality (j : (SingleObj G)ᵒᵖ) :
    (S1835BC.mapCone (S1830G2.invariantsCone K)).π.app j =
      (conePointIso K).hom ≫ (S1830G2.invariantsCone (K ⋙ S1835BC)).π.app j := by
  cases j
  rw [Functor.mapCone_π_app]
  apply ObjectProperty.hom_ext
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  rw [ObjectProperty.FullSubcategory.comp_hom, CommAlgCat.hom_comp, AlgHom.comp_apply]
  exact (conePointAlgEquiv_val K x).symm

/-- The base change of the invariants cone is the invariants cone of the base change. -/
noncomputable def coneIso :
    S1835BC.mapCone (S1830G2.invariantsCone K) ≅ S1830G2.invariantsCone (K ⋙ S1835BC) :=
  Cone.ext (conePointIso K) (coneIso_naturality K)

/-- The base change of the invariants cone is a limit cone.  This is the heart of
field 5: fixed points commute with the base change R' -> Omega. -/
noncomputable def isLimitMapCone :
    IsLimit (S1835BC.mapCone (S1830G2.invariantsCone K)) :=
  (S1830G2.invariantsIsLimit (R := S1835Omega) (K ⋙ S1835BC)).ofIsoLimit (coneIso K).symm

/-! ## 3. Preservation of limits and colimits of shape SingleObj G -/

/-- Base change R' -> Omega preserves limits indexed by the finite one-object groupoid
(SingleObj G)^op, i.e. it preserves G-fixed points. -/
noncomputable instance preservesLimitsOfShape_op_singleObj :
    PreservesLimitsOfShape (SingleObj G)ᵒᵖ S1835BC where
  preservesLimit {K'} :=
    { preserves := fun {c} hc =>
        ⟨(isLimitMapCone K').ofIsoLimit
          (((Cone.functoriality K' S1835BC).mapIso
            (hc.uniqueUpToIso (S1830G2.invariantsIsLimit K'))).symm)⟩ }

/-- Equivalently: (S1835BC).op preserves colimits indexed by SingleObj G, i.e. base
change preserves quotients by finite group actions. -/
noncomputable instance preservesColimitsOfShape_singleObj :
    PreservesColimitsOfShape (SingleObj G) (S1835BC).op :=
  preservesColimitsOfShape_op (J := SingleObj G) (F := S1835BC)

end Main

/-! ## 4. Field 5 of the six-field fibre functor -/

/-- Field 5, in the exact form stated in S1835. -/
theorem S1835BCPreservesQuotients_actual : S1835BCPreservesQuotients := by
  intro G _ _
  letI : Fintype G := Fintype.ofFinite G
  letI : DecidableEq G := Classical.decEq G
  exact preservesColimitsOfShape_singleObj (G := G)

/-- Field 5 for the actual geometric fibre functor at the closed point (0,0): the fibre
functor preserves quotients by finite group actions. -/
theorem S1851PreservesQuotients :
    ∀ (G : Type) [Group G] [Finite G],
      PreservesColimitsOfShape (SingleObj G) (S1835Fiber) :=
  S1835PreservesQuotients_of S1835BCPreservesQuotients_actual

/-! ## 5. Axiom audit -/

#print axioms S1851RPrimeQuotientsCompleteActual.conePointAlgEquiv_val
#print axioms S1851RPrimeQuotientsCompleteActual.coneIso_naturality
#print axioms S1851RPrimeQuotientsCompleteActual.coneIso
#print axioms S1851RPrimeQuotientsCompleteActual.isLimitMapCone
#print axioms S1851RPrimeQuotientsCompleteActual.preservesLimitsOfShape_op_singleObj
#print axioms S1851RPrimeQuotientsCompleteActual.preservesColimitsOfShape_singleObj
#print axioms S1851RPrimeQuotientsCompleteActual.S1835BCPreservesQuotients_actual
#print axioms S1851RPrimeQuotientsCompleteActual.S1851PreservesQuotients

end LeanFormal.IUT.XiFPaper.S1851RPrimeQuotientsCompleteActual
