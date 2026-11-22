import tmp.sheaf.xif.paper.Mzk1SignedCor312ContractActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract
import Mathlib.Tactic

/-!
# A734 dictionary checklist: `Cor312Conclusion` ↔ lana `Corollary312Variant`

Field-level checklist of the equalities needed to transport our signed StepXI
contract to the lana variant shape (`Iut.Corollary312Variant`, which is
`X.qPilot.lhs ≤ X.rhsData.rhs` over `Iut.Corollary312VariantData`; the lana module
is NOT compiled in this environment, so its side is represented by abstract
readouts `LanaSideReadouts` whose fields name the lana projections).

Each field of `VolumeDictionary` is a theorem to write (abc/hull lanes):
* `q_dict`      : `O.qSigned = L.qPilotLhs`        (q-pilot volume dictionary);
* `theta_dict`  : `O.thetaSigned = L.thetaPilotRhs` (theta-pilot volume dictionary);
* `target_dict` : `O.targetSigned = L.thetaPilotRhs` (intermediate target);
* `ipl_dict/she_dict/apt_dict` : wall-obligation dictionaries.

The concrete volume identities behind them are listed in `volumeDictionaryRows`
(with the candidate source objects).  No RETRACTED statement is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312VariantDictionaryChecklistShaActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1SignedCor312ContractActual

/-- Abstract lana-side readouts: the projections of `Corollary312VariantData`
(`X.qPilot.lhs`, `X.rhsData.rhs`, and the wall obligations hidden in `RHSData`). -/
structure LanaSideReadouts where
  qPilotLhs : Real
  thetaPilotRhs : Real
  iplLana : Prop
  sheLana : Prop
  aptLana : Prop

/-- Our-side readouts: the real fields of the signed StepXI contract. -/
structure OurSideReadouts where
  qSigned : Real
  thetaSigned : Real
  targetSigned : Real
  q_negative : qSigned < 0
  q_le_target : qSigned ≤ targetSigned
  target_le_theta : targetSigned ≤ thetaSigned
  ipl : Prop
  she : Prop
  apt : Prop

/-- Field-level volume/wall dictionary to be proved by abc/hull. -/
structure VolumeDictionary (L : LanaSideReadouts) (O : OurSideReadouts) where
  q_dict : O.qSigned = L.qPilotLhs
  theta_dict : O.thetaSigned = L.thetaPilotRhs
  target_dict : O.targetSigned = L.thetaPilotRhs
  ipl_dict : O.ipl ↔ L.iplLana
  she_dict : O.she ↔ L.sheLana
  apt_dict : O.apt ↔ L.aptLana

/-- The dictionary yields the lana variant shape. -/
theorem dictionary_variant_shape {L : LanaSideReadouts} {O : OurSideReadouts}
    (D : VolumeDictionary L O) :
    L.qPilotLhs ≤ L.thetaPilotRhs := by
  rw [← D.q_dict, ← D.theta_dict]
  exact le_trans O.q_le_target O.target_le_theta

/-- The dictionary yields our signed StepXI contract (evidence arguments for ipl/she/apt). -/
noncomputable def dictionary_to_contract {L : LanaSideReadouts} {O : OurSideReadouts}
    (_D : VolumeDictionary L O) (hipl : O.ipl) (hshe : O.she) (hapt : O.apt) :
    StepXIContract :=
  signedCor312Contract O.qSigned O.thetaSigned O.q_negative
    O.ipl hipl O.she hshe O.apt hapt (le_trans O.q_le_target O.target_le_theta)

/-- The dictionary yields `Cor312Conclusion` (the dictionary transports the shape to
the lana variant; the conclusion itself uses our ordered fields). -/
theorem dictionary_to_conclusion {L : LanaSideReadouts} {O : OurSideReadouts}
    (_D : VolumeDictionary L O) (hipl : O.ipl) (hshe : O.she) (hapt : O.apt) :
    Cor312Conclusion
      (signedCor312Contract O.qSigned O.thetaSigned O.q_negative
        O.ipl hipl O.she hshe O.apt hapt (le_trans O.q_le_target O.target_le_theta)) :=
  signedCor312_conclusion O.qSigned O.thetaSigned O.q_negative
    O.ipl hipl O.she hshe O.apt hapt (le_trans O.q_le_target O.target_le_theta)
structure DictionaryRow where
  fieldName : String
  statement : String
  sourceCandidate : String
  deriving Repr, DecidableEq

def volumeDictionaryRows : List DictionaryRow :=
  [ ⟨"q_dict", "O.qSigned = (X.qPilot.lhs : Real)",
     "q-pilot volume dictionary: procession-normalized log-volume of q vs our normalized rpVolume/signed log-volume (S3137/S1929 readings)"⟩
  , ⟨"theta_dict", "O.thetaSigned = (X.rhsData.rhs : Real)",
     "theta-pilot volume dictionary: procession-normalized hull log-volume vs our hull/fullRegion volume (s1902LogVolume / normalized Haar)"⟩
  , ⟨"target_dict", "O.targetSigned = (X.rhsData.rhs : Real)",
     "intermediate target identification (our signed assembly target = theta reading)"⟩
  , ⟨"normalization", "normalized log-volume convention agrees on the unit region",
     "our `s1902LogVolume unitRegion = 1`; lana procession normalization (RHSData/normalizedHvolVolume)"⟩
  , ⟨"q negativity", "X.qPilot.lhs < 0 (or O.q_negative + q_dict)",
     "q-pilot sign: our normalized `hqneg_norm`; lana admissibility fields of QPilotData"⟩
  , ⟨"theta admissibility", "lana RHSData hull-admissibility <-> our hullRegion containment",
     "our `rpRequirementNorm.possible_in_hull`/hull fields vs RHSData admissibility"⟩
  , ⟨"ipl/she/apt", "our ipl/she/apt Props <-> lana RHSData wall-obligation fields",
     "stepxi real statements (SHE etc.) instantiate the Props; lana hides them in data"⟩
  , ⟨"bridge scope", "no Lean bridge theorem exists between the two definitions",
     "this checklist is the field-level interface; lana module uncompiled here"⟩
  ]

theorem volumeDictionaryRows_length : volumeDictionaryRows.length = 8 := rfl

theorem volumeDictionaryRows_has_q_dict :
    volumeDictionaryRows.any (fun r => r.fieldName = "q_dict") = true := by
  decide

theorem volumeDictionaryRows_has_theta_dict :
    volumeDictionaryRows.any (fun r => r.fieldName = "theta_dict") = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1Cor312VariantDictionaryChecklistShaActual
