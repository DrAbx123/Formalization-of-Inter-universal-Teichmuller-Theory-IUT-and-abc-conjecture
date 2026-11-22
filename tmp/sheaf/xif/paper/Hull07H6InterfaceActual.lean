import tmp.sheaf.xif.paper.GenEll10bH6Mzk1WiringActual
import tmp.sheaf.xif.paper.S3182Cor312HullDetAssemblyActual
import tmp.sheaf.xif.paper.S3136ModelSourceClauseActual
import tmp.sheaf.xif.paper.S3136ModelNativeDataWithHaarActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-!
# STEP 0 prior-art: H6|Mzk1|GenEll transfer|HullDetAssemblyInputs -> hits GenEll10bH6Mzk1WiringActual:35/43/54/63 (H6Mzk1Witness, h6_genEll_transfer_of_mzk1, mzk1_thm25_of_core, h6_mzk1_interface), S3182Cor312HullDetAssemblyActual (HullDetAssemblyInputs/Cor312HullDetConclusion/cor312_hullDet_conditional) -> REUSE (hull-side H6 interface consumer; GeometricCore stays single named hypothesis; NO closure).

# [Hull] 07: hull-side H6 interface (H6 x Mzk1 consumer with the hull+det assembly)

Paper mapping: GenEll Thm 2.1 corpus 615-687 (chain 688-760); [Mzk1] Theorem 2.5
(Noncritical Belyi Maps) = single named deep input GeometricCore; downstream
IUT III Cor 3.12 statement corpus 10324-10353 / Step (xi) 10750-10987 /
conclusion 10897.
This file WIRES the hull+det assembly (S3182) with the H6 x Mzk1 interface
(GenEll10b) into one hull-side consumer.  HONESTY: H6 is conditional on the
[Mzk1] GeometricCore witness (single named deep hypothesis, proved := false in the
tree) and on the named H2/H4 inputs inside HullDetAssemblyInputs; this is an
interface/consumer wiring, NOT closure of H6 or Mzk1.  Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Hull07H6InterfaceActual

universe u

open LeanFormal.IUT.XiFPaper.S3132IVGenEllShadowAdapterActual
open LeanFormal.IUT.XiFPaper.GenEll10H6ClosureActual
open LeanFormal.IUT.XiFPaper.GenEll10bH6Mzk1WiringActual
open LeanFormal.IUT.XiFPaper.Mzk1GeometricCoreRealStructureActual
open LeanFormal.IUT.XiFPaper.Mzk1Thm25ConclusionActual
open LeanFormal.IUT.XiFPaper.S3182Cor312HullDetAssemblyActual
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S3136NativeHaarFamilyActual
open LeanFormal.IUT.XiFPaper.S3136ModelSourceClauseActual
open LeanFormal.IUT.XiFPaper.S3136ModelNativeDataWithHaarActual
open NeronModelInfra
open CategoryTheory AlgebraicGeometry

variable {l : PrimeGeFive}
variable (M : LGPModelSourceClauseMissing l)
variable [Fintype (Bad (nativePlaceSelection (lgpModelNativeData M)))]

/-- Hull-side H6 inputs: the hull+det assembly inputs plus the H6 x Mzk1 witness. -/
structure HullH6InterfaceInputs (Point : Type u) {R : Type u} [CommRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (T D : Set C) where
  hull : HullDetAssemblyInputs M
  h6 : H6Mzk1Witness Point c ε T D

/-- **Hull-side H6 consumer:** from the hull+det assembly inputs and the H6 x Mzk1
witness, get the Cor 3.12 hull+det conclusion AND the H6 transfer AND the [Mzk1]
Thm 2.5 conditional conclusion.  Every input field is consumed; GeometricCore
stays the single named hypothesis. -/
theorem hull_h6_interface {R : Type u} [CommRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (T D : Set C)
    (I : HullH6InterfaceInputs M PUnit c ε T D) :
    Cor312HullDetConclusion M I.hull.theta ∧
      (∃ lowerBound : ℝ, ∀ x : PUnit,
        lowerBound ≤ (1 + I.h6.shadow.epsilon) *
          (I.h6.shadow.logDiff x + I.h6.shadow.logCond x) - I.h6.shadow.height x) ∧
      (∃ W : Mzk1GeometricCoreWitness c ε T D,
        Mzk1Thm25Conclusion c ε T D W) :=
  ⟨cor312_hullDet_conditional M I.hull,
   h6_genEll_transfer_of_mzk1 c ε T D I.h6,
   mzk1_thm25_of_core c ε T D I.h6⟩

/-- Hull-side H6 interface rows. -/
def hullH6InterfaceRows : List (String × String) :=
  [ ("Hull+det Cor 3.12 hull-side comparison", "consumed via S3182 cor312_hullDet_conditional (conditional on named H2/H4 inputs)")
  , ("H6 GenEll transfer", "consumed via GenEll10b h6_genEll_transfer_of_mzk1 (interface-level, [Mzk1] GeometricCore single named hypothesis)")
  , ("[Mzk1] Thm 2.5 conditional conclusion", "consumed via GenEll10b mzk1_thm25_of_core; GeometricCore = deep named input, proved := false")
  , ("downstream context", "IUT III Cor 3.12 corpus 10324-10353; Step (xi) 10750-10987; conclusion 10897") ]

/-- The hull-side H6 interface record has four rows. -/
theorem hullH6InterfaceRows_length : hullH6InterfaceRows.length = 4 := rfl

#check HullH6InterfaceInputs
#check hull_h6_interface
#check hullH6InterfaceRows_length

end LeanFormal.IUT.XiFPaper.Hull07H6InterfaceActual
end