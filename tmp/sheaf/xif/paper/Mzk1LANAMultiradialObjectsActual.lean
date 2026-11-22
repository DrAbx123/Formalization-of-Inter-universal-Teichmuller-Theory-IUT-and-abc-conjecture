import tmp.sheaf.xif.paper.RefLANAMultiradialSpecActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# LANA latest Multiradial objects as Thm 3.11 statement-level data

Direct reference layer over `tmp.sheaf.lana_latest.Iut.Multiradial.Spec`:
raw output, (Ind1)x(Ind2) orbit representation, possible regions, Ind2 group,
and the Thm 3.11(i) functoriality shape.  The file does not rewrite LANA's
definitions; it packages them as a reusable object. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1LANAMultiradialObjectsActual

universe u v w w'

variable {G : Type u} [Groupoid.{v} G] {A : Type w'} [Group A]

/-- A LANA multiradial algorithm object: raw output plus a functorial choice of
multiradial representations. -/
structure Thm311MultiradialObject where
  raw : RawOutput.{u, v, w} G A
  alg : ∀ P : G, MRRep raw P
  functorial : IsFunctorialAlg raw alg

namespace Thm311MultiradialObject

variable (O : Thm311MultiradialObject (G := G) (A := A))

/-- The étale-picture/Thm 3.11(i) shape follows from the stored functoriality. -/
theorem thm311iShape (P : Int → G) (Φ : ∀ n n' : Int, Set (P n ⟶ P n')) :
    Thm311iShape O.raw O.alg P Φ :=
  thm311iShape_of_isFunctorial O.functorial P Φ

/-- The possible-region construction of the multiradial representation. -/
theorem possibleRegion_subset {P : G} {X : Type*}
    (reg : O.raw.F.obj P → Set X) (x : O.raw.F.obj P) :
    reg x ⊆ MRRep.possibleRegion (R := O.raw) reg (MRRep.mk (R := O.raw) x) :=
  MRRep.reg_subset_possibleRegion (R := O.raw) reg x

end Thm311MultiradialObject

/-- LANA's independent-copy (Ind2)-group, exposed as a named object. -/
abbrev Ind2Indeterminacy (lstar : Nat) (V : Type*) (Ism : V → Type*)
    [∀ v, Group (Ism v)] := Ind2Group lstar V Ism

/-- Specialization to one local place (single-copy input). -/
def ind2Single (lstar : Nat) (V : Type*) (Ism : V → Type*)
    [∀ v, Group (Ism v)] [DecidableEq V] {v : V} (x : Ism v) :
    Ind2Indeterminacy lstar V Ism := Ind2Group.single x

/-- The upper-semi (Ind3) compatible region relation. -/
theorem upperSemi_refl {X : Type*} (R : Set X) : UpperSemi R R := subset_rfl

theorem upperSemiCompatible_const {X : Type*} (R : Set X) :
    UpperSemiCompatible (fun _ => R) R := fun _ => upperSemi_refl R

end LeanFormal.IUT.XiFPaper.Mzk1LANAMultiradialObjectsActual

end
