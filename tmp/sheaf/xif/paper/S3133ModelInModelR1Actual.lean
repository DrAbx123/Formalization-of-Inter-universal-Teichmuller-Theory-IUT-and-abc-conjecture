import tmp.sheaf.xif.paper.S3133ModelSource31DataActual
import tmp.sheaf.xif.paper.S3133ModelM1PlaceToModActual
import tmp.sheaf.xif.paper.S3133ModelM2bDescentActual
import tmp.sheaf.xif.paper.S3133ModelHodgeTheaterActual
import tmp.sheaf.xif.paper.S3137ModelOriginalInputSkeletonActual
import tmp.sheaf.xif.paper.S3137ModelTheaterSkeletonActual

/-!
# In-model R1 composition (component/docs-level; not a paper object)

COMPONENT, not a paper object.  Named consumers: mainline/lattice in-model R1
record (docs only until a real closure triggers the single reopen).

In-model R1 status after this batch:
* M0/M3: proved for the frozen model map (S3133S3131GaussianModelComponentsActual,
  S3133GaussianModelMapResidualFinalActual).
* M1: CONSTRUCTED in-model (class A): explicit V_mod_bijection datum with
  injective place map (S3133ModelM1PlaceToModActual.
  S3133ModelM1_constructible).
* M2b: DEFINITIONAL in-model (class A): qVFamily defined from the model Tate
  q-parameter (=1/5), descent = rfl (S3133ModelM2bDescentActual.
  S3135ModelQVFam_descent, _abs_log).
* F4.a/F4.b: by construction from the model value package (abc) per audit.
* Remaining model-side input: an index-dependent theater family with
  distinctness and arithmetic alignment (lattice's formal obstruction: a
  constant theater cannot be injective for index Int x Int).  This is a
  model-construction input, not a paper-faithfulness residual; documented in
  S3137ModelTheaterSkeletonActual.

This file packages the composition interface: given that theater data, the
model OriginalInput is lattice's modelOriginalInputOfSkeleton; the in-model
M1/M2b data are the constructed ones above.
No sorry/axiom/toy.  WRITE-ONLY.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S3133ModelInModelR1Actual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3133ModelSource31DataActual
open LeanFormal.IUT.XiFPaper.S3133ModelM1PlaceToModActual
open LeanFormal.IUT.XiFPaper.S3133ModelM2bDescentActual
open LeanFormal.IUT.XiFPaper.S3133ModelHodgeTheaterActual
open LeanFormal.IUT.XiFPaper.S3133ModelVBasisActual
open LeanFormal.IUT.XiFPaper.S3137ModelTheaterSkeletonActual
open LeanFormal.IUT.XiFPaper.S3137ModelOriginalInputSkeletonActual
open LeanFormal.IUT.XiFPaper.S3136ModelThetaPacketActual

variable {l : PrimeGeFive}

/-- The in-model R1 composition data: source contract providers, the model
theater-family data with distinctness/alignment, and the constructed in-model M1
datum. -/
structure S3133ModelR1Composition where
  providers : S3136SourceDefinition31DataAssemblyAdapterActual.LGPSource31SlotProviders l
  theaterData : ModelTheaterData.{0, 0, 0, 0, 0} (l := l) (V := S3135ModelV)
  theater_injective : Function.Injective theaterData.theater
  arithmetic_align : ∀ i,
    (theaterData.theater i).arithmetic = (modelSource31Data providers).arithmetic
  m1 : S3133ModelPlaceToModDatum

/-- The model OriginalInput assembled from the composition data (via lattice's
skeleton): this is the in-model same-C input. -/
noncomputable def S3133ModelR1Composition.originalInput
    (C : S3133ModelR1Composition (l := l)) :
    OriginalInput.{0, 0, 0, 0, 0} l S3135ModelV :=
  modelOriginalInputOfSkeleton.{0, 0, 0, 0, 0}
    (modelSource31Data C.providers) C.theaterData C.theater_injective
    C.arithmetic_align

/-- In-model R1 status (documented as a Prop): M1 constructed, M2b definitional,
plus the theater-family input. -/
def S3133ModelR1Status : Prop :=
  (∃ D : S3133ModelPlaceToModDatum, Function.Injective D.placeOf) ∧
    (∀ (l : PrimeGeFive) (data : LeanFormal.IUT.XiFPaper.S3135ModelValueDataActual.S3135ModelValueData)
      (v : S3135ModelV),
      (LeanFormal.IUT.XiFPaper.S3133ModelM2bDescentActual.S3135ModelQVFam l data v =
        LeanFormal.IUT.XiFPaper.S3133ModelM2bDescentActual.S3135ModelQValue l data))

/-- The documented in-model R1 status holds: M1 is constructed and the M2b
descent is definitional. -/
theorem S3133ModelR1Status_holds : S3133ModelR1Status :=
  ⟨S3133ModelM1_constructible, fun _ _ _ => rfl⟩

end LeanFormal.IUT.XiFPaper.S3133ModelInModelR1Actual
