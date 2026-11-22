import tmp.sheaf.xif.paper.Mzk1Thm25WiringActual
import tmp.sheaf.xif.paper.Mzk1GChoiceScaleActual
import tmp.sheaf.xif.paper.GenEll10bH6Mzk1WiringActual
import tmp.sheaf.xif.paper.S3182Cor312HullDetAssemblyActual
import tmp.sheaf.xif.paper.S3136ModelSourceClauseActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-!
# STEP 0 prior-art: H6 upgrade|Mzk1 Thm2.5|Lemma22|Lemma24|GeometricCore|scale_realHypotheses -> hits Mzk1Thm25WiringActual:104-161 (Thm25WiringRecord, thm25_wiring, thm25_of_22_24_and_geometricCore, rows/residual), Mzk1GChoiceScaleActual:233 scale_realHypotheses_exists (ScaleRealHypotheses DISCHARGED per A160), GenEll10bH6Mzk1WiringActual:35-71 (H6Mzk1Witness/h6_genEll_transfer_of_mzk1/h6_mzk1_interface), S3182Cor312HullDetAssemblyActual -> REUSE (H6 upgraded consumer; 2.2/2.4/GeometricCore remain named hypotheses; no closure).

# [Hull] 11: H6 support upgrade - Mzk1 Thm 2.5 wiring + GenEll transfer + Cor 3.12 consumer

Paper mapping: GenEll Thm 2.1 corpus 615-687 (chain 688-760); [Mzk1] Lemma 2.2/2.4
and Theorem 2.5 corpus 207-221 / proof 222-281; IUT III Cor 3.12 statement corpus
10324-10353; Step (xi) 10750-10987; conclusion 10897.
UPGRADE vs Hull07: instead of the plain GeometricCore witness, this consumer
takes the Mzk1Thm25Wiring reduction inputs (full Lemma 2.2 StatementShape,
Lemma 2.4 shape, GeometricCore recast) and derives the Thm 2.5 conditional
conclusion through the PROVED GeometricCore => conclusion step, together with the
H6 GenEll transfer and the Cor 3.12 hull+det conclusion.
HONESTY: Lemma22FullStatementShape, Lemma24Shape and GeometricCore recast stay the
named reduction/deep hypotheses (stage4 replaces 2.2; 2.4 F/D/M and GeometricCore
existence remain open); ScaleRealHypotheses is DISCHARGED in Mzk1GChoiceScaleActual
(A160) and is cited, not re-proved.  No closure claim.  Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Hull11H6Mzk1UpgradeActual

universe u

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S3136NativeHaarFamilyActual
open LeanFormal.IUT.XiFPaper.S3136ModelSourceClauseActual
open LeanFormal.IUT.XiFPaper.S3136ModelNativeDataWithHaarActual
open LeanFormal.IUT.XiFPaper.S3132IVGenEllShadowAdapterActual
open LeanFormal.IUT.XiFPaper.GenEll10H6ClosureActual
open LeanFormal.IUT.XiFPaper.GenEll10bH6Mzk1WiringActual
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCoreRealStructureActual
open LeanFormal.IUT.XiFPaper.Mzk1Thm25ConclusionActual
open LeanFormal.IUT.XiFPaper.Mzk1Thm25WiringActual
open LeanFormal.IUT.XiFPaper.S3182Cor312HullDetAssemblyActual
open NeronModelInfra
open CategoryTheory AlgebraicGeometry

variable {l : PrimeGeFive}
variable (M : LGPModelSourceClauseMissing l)
variable [Fintype (Bad (nativePlaceSelection (lgpModelNativeData M)))]

/-- H6 upgrade inputs: Cor 3.12 hull+det assembly inputs, the GenEll shadow, and the
Mzk1 Thm 2.5 reduction inputs (2.2 shape, 2.4 shape, GeometricCore recast). -/
structure HullH6UpgradeInputs (Point : Type u) {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (T D : Set C) where
  hull : HullDetAssemblyInputs M
  shadow : AdaptedIVGenEllShadow Point
  h22 : Lemma22FullStatementShape
  h24 : Lemma24Shape.{u}
  hcore : Mzk1GeometricCoreRecast c ε T D

/-- **H6 upgrade consumer:** from the hull+det assembly, the GenEll shadow and the
Mzk1 Thm 2.5 reduction inputs, get the Cor 3.12 hull+det conclusion AND the H6
GenEll transfer AND the [Mzk1] Thm 2.5 conditional conclusion.  Every field is
consumed; the reduction hypotheses stay named (no closure). -/
theorem hull11_h6_upgrade (Point : Type u) {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (T D : Set C)
    (In : HullH6UpgradeInputs (l := l) M Point c ε T D) :
    Cor312HullDetConclusion M In.hull.theta ∧
      (∃ lowerBound : ℝ, ∀ x : Point,
        lowerBound ≤ (1 + In.shadow.epsilon) *
          (In.shadow.logDiff x + In.shadow.logCond x) - In.shadow.height x) ∧
      (∃ W : Mzk1GeometricCoreWitness c ε T D,
        Mzk1Thm25Conclusion c ε T D W) :=
  ⟨cor312_hullDet_conditional M In.hull,
   h6_genEll_transfer_of_mzk1 c ε T D ⟨In.shadow, In.hcore⟩,
   thm25_of_22_24_and_geometricCore c ε T D In.h22 In.h24 In.hcore⟩

/-- The Mzk1 Thm 2.5 reduction inputs are exactly the named hypotheses of the
wiring record; this projection records the dependency (no re-proof). -/
theorem hull11_thm25_wiring_projection {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (T D : Set C)
    (h22 : Lemma22FullStatementShape) (h24 : Lemma24Shape.{u})
    (hcore : Mzk1GeometricCoreRecast c ε T D) :
    ∃ W : Mzk1GeometricCoreWitness c ε T D, Mzk1Thm25Conclusion c ε T D W :=
  thm25_of_22_24_and_geometricCore c ε T D h22 h24 hcore

/-- H6 support status rows after this upgrade. -/
def hull11Rows : List (String × String × String) :=
  [ ("GenEll H6 transfer (shadow-level)", "A", "CONSUMED GenEll10b h6_genEll_transfer_of_mzk1 (PROVED interface-level)")
  , ("GeometricCore => Thm 2.5 conclusion", "A", "CONSUMED Mzk1Thm25ConclusionActual.mzk1Thm25Conclusion_of_geometricCore (PROVED)")
  , ("full Lemma 2.2 StatementShape (paper-conditioned)", "B", "NAMED; stage4 replaces (Mzk1PolyChainRuleActual + induction)")
  , ("Lemma 2.4 shape", "B", "NAMED; 2.4 F/D/M open at stage4/mainline")
  , ("GeometricCore recast existence", "B", "NAMED class-D paper input (real-structure skeleton)")
  , ("ScaleRealHypotheses (Lemma 2.2 scale side)", "A", "DISCHARGED in Mzk1GChoiceScaleActual:233 scale_realHypotheses_exists (A160); cited, not re-proved")
  , ("Cor 3.12 hull+det conclusion", "A", "CONSUMED S3182 cor312_hullDet_conditional") ]

/-- The H6 upgrade row record has seven rows. -/
theorem hull11Rows_length : hull11Rows.length = 7 := rfl

#check HullH6UpgradeInputs
#check hull11_h6_upgrade
#check hull11_thm25_wiring_projection
#check hull11Rows_length

end LeanFormal.IUT.XiFPaper.Hull11H6Mzk1UpgradeActual
end