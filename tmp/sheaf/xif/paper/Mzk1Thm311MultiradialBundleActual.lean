/- Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. -/
import tmp.sheaf.xif.paper.RefLANAMultiradialSpecActual
import Mathlib.Tactic

/-! A516: Thm 3.11 multiradial object bundle, reusing the local LANA
Multiradial/Spec copy (RawOutput, MRRep, IsFunctorialAlg, possibleRegion,
Procession, Ind2/Ind3). Composition only; no new axioms. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1Thm311MultiradialBundleActual

open CategoryTheory
open Iut.Multiradial

universe u v w w'

variable {G : Type u} [Groupoid.{v} G] {A : Type w'} [Group A]

/-- Thm 3.11(i) multiradial object: raw output, multiradial representation choice
for every input, and its functoriality. -/
structure Thm311MultiradialBundle where
  raw : RawOutput.{u, v, w} G A
  alg : forall P : G, MRRep raw P
  functorial : IsFunctorialAlg raw alg

namespace Thm311MultiradialBundle

variable (B : Thm311MultiradialBundle (G := G) (A := A))

/-- Thm 3.11(i) étale-picture shape from the stored functoriality. -/
theorem thm311iShape (P : Int -> G) (Phi : forall n n' : Int, Set (P n ⟶ P n')) :
    Thm311iShape B.raw B.alg P Phi :=
  thm311iShape_of_isFunctorial B.functorial P Phi

/-- The possible images of a region-valued construction over a multiradial
representation (Cor 3.12 Step (x)). -/
def possibleImages {P : G} {X : Type*} (reg : B.raw.F.obj P -> Set X)
    (r : MRRep B.raw P) : Set X :=
  MRRep.possibleRegion reg r

theorem region_subset_possibleImages {P : G} {X : Type*}
    (reg : B.raw.F.obj P -> Set X) (x : B.raw.F.obj P) :
    reg x <= B.possibleImages reg (MRRep.mk (R := B.raw) x) :=
  MRRep.reg_subset_possibleRegion reg x

/-- Monotonicity of possible images in the region construction. -/
theorem possibleImages_mono {P : G} {X : Type*}
    {reg1 reg2 : B.raw.F.obj P -> Set X}
    (h : forall x, reg1 x <= reg2 x) (r : MRRep B.raw P) :
    B.possibleImages reg1 r <= B.possibleImages reg2 r := by
  intro y hy
  rw [Thm311MultiradialBundle.possibleImages, MRRep.possibleRegion] at hy ⊢
  simp only [Set.mem_iUnion] at hy ⊢
  rcases hy with ⟨x, hx, hyx⟩
  exact ⟨x, hx, h x hyx⟩

end Thm311MultiradialBundle

/-! ## Ind2 / Ind3 object re-exports -/

/-- The independent-copy (Ind2) group of a nonzero bad place. -/
abbrev Ind2Indeterminacy (lstar : Nat) (V : Type*) (Ism : V -> Type*)
    [forall v, Group (Ism v)] := Ind2Group lstar V Ism

/-- Single independent copy. -/
def ind2Single (lstar : Nat) (V : Type*) (Ism : V -> Type*)
    [forall v, Group (Ism v)] [DecidableEq V] {v : V} (x : Ism v) :
    Ind2Indeterminacy lstar V Ism :=
  Ind2Group.single x

/-- Upper-semi (Ind3) compatibility of a vertical family with a region. -/
def ind3FamilyCompatible {X : Type*} (img : Int -> Set X) (R : Set X) : Prop :=
  UpperSemiCompatible img R

theorem ind3Family_iUnion_subset {X : Type*} {img : Int -> Set X} {R : Set X}
    (h : ind3FamilyCompatible img R) : (⋃ m, img m) <= R :=
  UpperSemiCompatible.iUnion_subset h

theorem ind3_sUnion {X : Type*} (R : Set X) : ⋃₀ ind3Possible R = R := sUnion_ind3Possible R

end LeanFormal.IUT.XiFPaper.Mzk1Thm311MultiradialBundleActual