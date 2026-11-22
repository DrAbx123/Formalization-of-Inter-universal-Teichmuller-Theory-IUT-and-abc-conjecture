import tmp.sheaf.xif.paper.S3136BDClassChainToolActual
noncomputable section
open LeanFormal.IUT

namespace LeanFormal.IUT.XiFPaper.GenEll04Prop17Actual

open LeanFormal.IUT.XiFPaper.S3136BDClassChainToolActual

/-- Prop 1.7(i) (Conductors and Log Differents, corpus 524-554): for the stated
generically finite morphism and divisors with ramification index dividing e:
log-cond_E - log-cond_D <=~ log-diff_Y - log-diff_Z <=~ (1 - 1/e) * log-cond_E on UY(Q). -/
def Prop17LogDiffInequality {Y : Type} (UYQ : Set Y)
    (logCondE logCondD logDiffY logDiffZ : Y → Real) (e : Nat) : Prop :=
  IsBDLe (fun y => logDiffY y - logDiffZ y) (fun y => logCondE y - logCondD y) UYQ ∧
    IsBDLe (fun y => ((1 : Real) - 1 / (e : Real)) * logCondE y)
      (fun y => logDiffY y - logDiffZ y) UYQ

/-- Prop 1.7(ii) (corpus 555-564): Riemann-Hurwitz degree relation for omega(-) when
all ramification indices equal e (stated as an abstract real equation shape). -/
def Prop17DegreeFormula (degOmegaY degOmegaYDQ degOmegaZEQ degOYDQ degOZEQ : Real)
    (e : Nat) : Prop :=
  degOmegaY = degOmegaYDQ - degOYDQ ∧
    degOmegaY = degOmegaZEQ * (1 - degOZEQ / ((e : Real) * degOmegaZEQ))

/-- The exact Prop 1.7 statement shape. -/
def Proposition17Statement {Y : Type} (UYQ : Set Y)
    (logCondE logCondD logDiffY logDiffZ : Y → Real) (e : Nat)
    (degOmegaY degOmegaYDQ degOmegaZEQ degOYDQ degOZEQ : Real) : Prop :=
  Prop17LogDiffInequality UYQ logCondE logCondD logDiffY logDiffZ e ∧
    Prop17DegreeFormula degOmegaY degOmegaYDQ degOmegaZEQ degOYDQ degOZEQ e

/-- Elementary extraction: Prop 1.7 yields the first (difference) BD inequality. -/
theorem prop17_logDiff_of_statement {Y : Type} {UYQ : Set Y}
    {logCondE logCondD logDiffY logDiffZ : Y → Real} {e : Nat}
    {d1 d2 d3 d4 d5 : Real}
    (h : Proposition17Statement UYQ logCondE logCondD logDiffY logDiffZ e
      d1 d2 d3 d4 d5) :
    IsBDLe (fun y => logDiffY y - logDiffZ y)
      (fun y => logCondE y - logCondD y) UYQ :=
  h.1.1

def s3135Prop17Citations : List (String × String) :=
  [ ("Prop 1.7(i)", "corpus 524-554: log-cond_E - log-cond_D <=~ log-diff_Y - log-diff_Z <=~ (1 - 1/e) log-cond_E on UY(Q); elementary different theory + wild-ramification boundedness claim"),
    ("Prop 1.7(ii)", "corpus 555-564: Riemann-Hurwitz degree relation when ramification indices equal e") ]

theorem s3135Prop17Citations_length : s3135Prop17Citations.length = 2 := rfl

#check Proposition17Statement
#check prop17_logDiff_of_statement

end LeanFormal.IUT.XiFPaper.GenEll04Prop17Actual
end