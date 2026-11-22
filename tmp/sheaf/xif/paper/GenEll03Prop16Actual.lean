import tmp.sheaf.xif.paper.S3136BDClassChainToolActual
noncomputable section
open LeanFormal.IUT

namespace LeanFormal.IUT.XiFPaper.GenEll03Prop16Actual

open LeanFormal.IUT.XiFPaper.S3136BDClassChainToolActual

/-- Prop 1.6 (Conductor Bounded by the Height, corpus 505-523): for an effective
Cartier divisor D, L = O_X(D), and log-cond_D, ht_D, one has log-cond_D <=~ ht_D on
U(Q) = (X minus D)(Q).  Encoded with the tree BD tool on the point set UQ. -/
def Prop16ConductorBoundedByHeight {X : Type} (UQ : Set X)
    (logCondD htD : X → Real) : Prop :=
  IsBDLe htD logCondD UQ

/-- Elementary reuse of the BD algebra: transitivity of the BD relation. -/
theorem prop16_trans {X : Type} {UQ : Set X} {logCondD htD g : X → Real}
    (h1 : Prop16ConductorBoundedByHeight UQ logCondD htD)
    (h2 : IsBDLe logCondD g UQ) :
    IsBDLe htD g UQ :=
  isBDLe_trans h1 h2

def s3135Prop16Citations : List (String × String) :=
  [ ("Prop 1.6", "corpus 505-523: log-cond_D <=~ ht_D on U(Q); elementary proof from Def 1.5(iv) at nonarchimedean places and boundedness of |s| on compact X_arc at archimedean places") ]

theorem s3135Prop16Citations_length : s3135Prop16Citations.length = 1 := rfl

#check Prop16ConductorBoundedByHeight
#check prop16_trans

end LeanFormal.IUT.XiFPaper.GenEll03Prop16Actual
end