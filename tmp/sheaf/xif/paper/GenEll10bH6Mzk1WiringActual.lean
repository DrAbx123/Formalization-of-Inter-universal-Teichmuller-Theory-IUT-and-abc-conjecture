import tmp.sheaf.xif.paper.GenEll10H6ClosureActual
import tmp.sheaf.xif.paper.Mzk1Thm25ConclusionActual

/-! # GenEll10b: H6 x [Mzk1] wiring — H6 transfer + Thm 2.5 conditional conclusion

This file WIRES the two remaining H6-relevant interfaces into one consumer:
  * GenEll H6 transfer (interface-level `AdaptedIVGenEllShadow.exists_lowerBound`), and
  * [Mzk1] Theorem 2.5 conditional conclusion from the real-structure witness
    (`Mzk1GeometricCoreRecast` = Nonempty witness; conclusion read from witness fields).

Paper mapping: GenEll Thm 2.1 corpus 615-687 ((ii)=>(i) chain 688-760); [Mzk1] Theorem 2.5
(Noncritical Belyi Maps, corpus text) = single named deep input GeometricCore; IUT III
Corollary 3.12 statement corpus 10324-10353 / proof 10354-10987 / Step (xi) 10750-10987
(conclusion 10897) is the downstream consumer context.

HONESTY: this is an interface/consumer wiring, NOT a proof of [Mzk1] existence and NOT
H6 closure by GenEll: GeometricCore recast witness stays the single named hypothesis.
Registry frozen 14041; no registry edits. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.GenEll10bH6Mzk1WiringActual

universe u

open LeanFormal.IUT.XiFPaper.S3132IVGenEllShadowAdapterActual
open LeanFormal.IUT.XiFPaper.GenEll10H6ClosureActual
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCoreRealStructureActual
open LeanFormal.IUT.XiFPaper.Mzk1Thm25ConclusionActual
open NeronModelInfra
open CategoryTheory AlgebraicGeometry

/-- Combined H6 evidence bundle: GenEll shadow data plus the [Mzk1] GeometricCore
real-structure witness (single named deep hypothesis). -/
structure H6Mzk1Witness (Point : Type u) {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (T D : Set C) where
  shadow : AdaptedIVGenEllShadow Point
  core : Mzk1GeometricCoreRecast c ε T D

/-- H6 transfer re-exported through the combined witness (no new proof content;
reuses `h6_genEll_transfer`). -/
theorem h6_genEll_transfer_of_mzk1 {Point : Type u} {R : Type u} [CommRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (T D : Set C)
    (w : H6Mzk1Witness Point c ε T D) :
    ∃ lowerBound : ℝ, ∀ x : Point,
      lowerBound ≤ (1 + w.shadow.epsilon) * (w.shadow.logDiff x + w.shadow.logCond x) -
        w.shadow.height x :=
  h6_genEll_transfer w.shadow

/-- [Mzk1] Thm 2.5 conditional conclusion re-exported through the combined witness:
GeometricCore witness is the SINGLE named hypothesis (NOT unconditional). -/
theorem mzk1_thm25_of_core {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (T D : Set C)
    (w : H6Mzk1Witness PUnit c ε T D) :
    ∃ W : Mzk1GeometricCoreWitness c ε T D, Mzk1Thm25Conclusion c ε T D W :=
  mzk1Thm25Conclusion_of_geometricCore c ε T D w.core

/-- Combined H6 interface verdict: H6 transfer holds relative to the GenEll shadow, AND
the [Mzk1] Thm 2.5 conclusion holds relative to the GeometricCore witness. -/
theorem h6_mzk1_interface {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (T D : Set C)
    (w : H6Mzk1Witness PUnit c ε T D) :
    (∃ lowerBound : ℝ, ∀ x : PUnit,
      lowerBound ≤ (1 + w.shadow.epsilon) * (w.shadow.logDiff x + w.shadow.logCond x) -
        w.shadow.height x) ∧
    (∃ W : Mzk1GeometricCoreWitness c ε T D, Mzk1Thm25Conclusion c ε T D W) :=
  ⟨h6_genEll_transfer_of_mzk1 c ε T D w, mzk1_thm25_of_core c ε T D w⟩

/-- H6 x Mzk1 wiring rows (route slot, evidence, exact scope/paper line). -/
def h6Mzk1WiringRows : List (String × String × String) :=
  [ ("H6.transfer", "h6_genEll_transfer (GenEll10H6ClosureActual) re-exported; interface-level", "GenEll Thm 2.1 corpus 615-687; chain 688-760"),
    ("Mzk1.Thm25", "mzk1Thm25Conclusion_of_geometricCore through H6Mzk1Witness.core (single named hypothesis)", "[Mzk1] Theorem 2.5; GeometricCore = deep input (proved := false)"),
    ("H6.interface", "h6_mzk1_interface = conjunction of the two (this file)", "conditional consumer; NOT closure of GenEll or Mzk1"),
    ("downstream", "IUT III Cor 3.12 consumer context", "corpus 10324-10353 statement; 10354-10987 proof; Step (xi) 10750-10987, conclusion 10897") ]

theorem h6Mzk1WiringRows_length : h6Mzk1WiringRows.length = 4 := rfl

#check h6_genEll_transfer_of_mzk1
#check mzk1_thm25_of_core
#check h6_mzk1_interface

end LeanFormal.IUT.XiFPaper.GenEll10bH6Mzk1WiringActual
end