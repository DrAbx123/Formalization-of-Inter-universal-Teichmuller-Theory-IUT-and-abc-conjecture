import LeanFormal.IUT.Audit.Status

/-! # S3131 IUT IV Cor 2.2 / Cor 2.3 paper-input schemas + citations -/

namespace LeanFormal.IUT.XiFPaper.S3131IUTIVCor22Cor23InputActual

/-- Cor 2.2 (Construction of Suitable Initial Theta-Data) shape: existence of initial
Theta-data satisfying the (star j-inv) condition (corpus line 2380). -/
def Cor22Statement (hasSuitableInitialThetaData : Prop) : Prop :=
  hasSuitableInitialThetaData

/-- Cor 2.3 (Diophantine Inequalities) shape: Theorem A inequality for the curve X
constructed from the suitable initial Theta-data (corpus line 3117). -/
def Cor23Statement (theoremAInequality : Prop) : Prop :=
  theoremAInequality

def S3131IUTIVCitationRows : List (String × String) :=
  [ ("Theorem A", "corpus lines 93-112 (BD-class inequality ht_omega(D) <~ (1+eps)(log-diff + log-cond); ABC/Vojta/Szpiro special cases)"),
    ("Theorem 1.10", "corpus lines 1255-1300 (log-volume estimates for Theta-pilot objects; initial Theta-data, Cor 3.12 situation)"),
    ("Corollary 2.2", "corpus line 2380 (construction of suitable initial Theta-data)"),
    ("Corollary 2.3", "corpus line 3117 (Diophantine inequalities; proof completes line 3155)") ]

theorem S3131IUTIVCitationRows_length : S3131IUTIVCitationRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.S3131IUTIVCor22Cor23InputActual