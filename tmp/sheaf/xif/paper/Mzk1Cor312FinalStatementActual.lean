import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract
import tmp.sheaf.xif.paper.Mzk1Signed312AssemblyActual
import tmp.sheaf.xif.paper.Mzk1SignedCor312ContractActual

/-! # Cor 3.12 final statement shape (paper IUT III:10324-10353) -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalStatementActual

open LeanFormal.IUT

/-- Paper q-pilot signed log-volume: `-|log q|`. -/
def paperSignedQ (qMag : Real) : Real := -qMag

/-- Paper Theta-pilot signed log-volume: `-|log Theta|`. -/
def paperSignedTheta (thetaMag : Real) : Real := -thetaMag

/-- Paper target: `-|log q| ≤ -|log Theta|`. -/
def paperTarget (qMag thetaMag : Real) : Prop :=
  paperSignedQ qMag ≤ paperSignedTheta thetaMag

/-- Equivalent magnitude form: `|log Theta| ≤ |log q|`. -/
theorem paperTarget_iff_magnitudes (qMag thetaMag : Real) :
    paperTarget qMag thetaMag ↔ thetaMag ≤ qMag := by
  unfold paperTarget paperSignedQ paperSignedTheta
  constructor <;> intro h <;> linarith

/-- A contract with the paper signed slots satisfies the paper target exactly when
its `Cor312Conclusion` holds. -/
theorem contract_matches_paperTarget {C : StepXIContract} {qMag thetaMag : Real}
    (hq : C.qSigned = paperSignedQ qMag)
    (ht : C.thetaSigned = paperSignedTheta thetaMag) :
    Cor312Conclusion C ↔ paperTarget qMag thetaMag := by
  unfold Cor312Conclusion paperTarget
  simp only [hq, ht]

/-- Contract target identity: `targetSigned = thetaSigned` by construction; the
comparison content is in `q_le_target`, not in this identity. -/
theorem signedContract_target_identity (q theta : Real) (hq : q < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) (hle : q ≤ theta) :
    (LeanFormal.IUT.XiFPaper.Mzk1SignedCor312ContractActual.signedCor312Contract
      q theta hq ipl hipl she hshe apt hapt hle).targetSigned = theta := rfl

end LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalStatementActual
