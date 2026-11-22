import tmp.sheaf.xif.paper.S3130QCSourceActual
import tmp.sheaf.xif.paper.NativeQVPilotNormalizedLogVolumeActual
import tmp.sheaf.xif.paper.QVFamThetaImageActual

/-! # S3131: same-C Batch A source input identification

Fixed qualified input C for Batch A is the actual native Theta-data T together
with the exact paper prime alignment S2135PrimeAlignmentRequired at every bad
place.  The q-side data family S3130QCSourceData (S3130QCSourceActual) is the
actual clause-B qVFamily readout.  This file records the same-C identifications:

* qSourceFamily_qV: every bad place b reads the same actual qVFamily T b;
* qSourceFamily_qNorm: every bad place b reads the same actual qVFamilyQNorm;
* weight_eq_inv: the actual procession weight nativeBadLocalWeight T b is the
  inverse actual completion degree [K_w : (F_mod)_v] of IUT III Remark 3.1.1(ii)
  (corpus lines 5419-5433);
* qSourceFamily_chain: the O^x-mu chain carried by the same data is the actual
  s2321OUnitsChainOfPrimeAlignment.

This is object identification only: no inequality is asserted here.
Sources: IUT III Remark 3.1.1(ii) (corpus lines 5408-5465); IUT III
Definition 3.8(i) and Corollary 3.12 (corpus lines 10324-10353);
coord/ROADMAP-2026-11-02.md Batch A.  No sorry/axiom/True/PUnit.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S3131SameCSourceInputActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.S3130QCSourceActual
open LeanFormal.IUT.XiFPaper.S2219PaperOUnitsCarrierActual
open LeanFormal.IUT.XiFPaper.S2321OUnitsChainFinalActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.ProcessionNormalizationWeightsActual
open LeanFormal.IUT.XiFPaper.NativeQVPilotNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.QVFamThetaImageActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- The actual q-side source data of the same fixed input at one bad place,
conditional on the exact paper prime alignment at that place. -/
noncomputable def qSourceFamily
    (hAlign : forall b : Bad (nativePlaceSelection T),
      LeanFormal.IUT.XiFPaper.S2135Layer1SplitActual.S2135PrimeAlignmentRequired T b)
    (b : Bad (nativePlaceSelection T)) :
    S3130QCSourceData T b (hAlign b) :=
  s3130QCSourceData T b (hAlign b)

/-- Same-C identification: the q-side source data reads the same actual
clause-B q parameter as the q-pilot family. -/
theorem qSourceFamily_qV
    (hAlign : forall b : Bad (nativePlaceSelection T),
      LeanFormal.IUT.XiFPaper.S2135Layer1SplitActual.S2135PrimeAlignmentRequired T b)
    (b : Bad (nativePlaceSelection T)) :
    (qSourceFamily T hAlign b).qV = qVFamily T b :=
  s3130QCSourceData_qV T b (hAlign b)

/-- Same-C identification: the q-side source data reads the same actual norm. -/
theorem qSourceFamily_qNorm
    (hAlign : forall b : Bad (nativePlaceSelection T),
      LeanFormal.IUT.XiFPaper.S2135Layer1SplitActual.S2135PrimeAlignmentRequired T b)
    (b : Bad (nativePlaceSelection T)) :
    (qSourceFamily T hAlign b).qNorm = qVFamilyQNorm T b :=
  s3130QCSourceData_qNorm T b (hAlign b)

/-- Same-C identification: the O^x-mu chain is the actual chain. -/
theorem qSourceFamily_chain
    (hAlign : forall b : Bad (nativePlaceSelection T),
      LeanFormal.IUT.XiFPaper.S2135Layer1SplitActual.S2135PrimeAlignmentRequired T b)
    (b : Bad (nativePlaceSelection T)) :
    (qSourceFamily T hAlign b).chain =
      s2321OUnitsChainOfPrimeAlignment T b (hAlign b) :=
  s3130QCSourceData_chain T b (hAlign b)

/-- Same-C identification: the quotient map is the actual S2219 quotient map. -/
theorem qSourceFamily_quotientMap
    (hAlign : forall b : Bad (nativePlaceSelection T),
      LeanFormal.IUT.XiFPaper.S2135Layer1SplitActual.S2135PrimeAlignmentRequired T b)
    (b : Bad (nativePlaceSelection T)) :
    (qSourceFamily T hAlign b).quotientMap = s2219QuotientMap T b :=
  s3130QCSourceData_quotientMap T b (hAlign b)

/-- The actual procession weight of a bad place is the inverse actual
completion degree [K_w : (F_mod)_v] (IUT III Remark 3.1.1(ii)). -/
theorem weight_eq_inv (b : Bad (nativePlaceSelection T)) :
    nativeBadLocalWeight T b =
      ((localCompletionDegree T.arithmetic (nativeBadToKPlace T b) : Nat) : Real)⁻¹ :=
  nativeBadLocalWeight_eq_inv T b

/-- The actual q norm of a bad place is the norm of the actual q parameter. -/
theorem qNorm_eq_norm (b : Bad (nativePlaceSelection T)) :
    qVFamilyQNorm T b = ‖(qVFamily T b).q‖ := rfl

/-- The actual q norm is positive. -/
theorem qNorm_pos (b : Bad (nativePlaceSelection T)) :
    0 < qVFamilyQNorm T b :=
  qVFamilyQNorm_pos T b

/-- The exact source condition of Batch A: the paper prime alignment exists at
every bad place.  This is recorded, not asserted. -/
def PrimeAlignmentFamily : Prop :=
  forall b : Bad (nativePlaceSelection T),
    LeanFormal.IUT.XiFPaper.S2135Layer1SplitActual.S2135PrimeAlignmentRequired T b

/-- The alignment family is exactly the source condition. -/
theorem primeAlignmentFamily_iff : PrimeAlignmentFamily T ↔
    (forall b : Bad (nativePlaceSelection T),
      LeanFormal.IUT.XiFPaper.S2135Layer1SplitActual.S2135PrimeAlignmentRequired T b) :=
  Iff.rfl

#check qSourceFamily_qV
#check weight_eq_inv

end LeanFormal.IUT.XiFPaper.S3131SameCSourceInputActual

end
