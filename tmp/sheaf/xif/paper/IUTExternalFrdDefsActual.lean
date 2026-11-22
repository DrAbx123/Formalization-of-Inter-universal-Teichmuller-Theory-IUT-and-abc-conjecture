import LeanFormal.IUT.IUTII.Frobenioid.DivisorialMonoidMinimalReplacement

/-! # IUTExternalFrdDefsActual — E3 [FrdI-II] Frobenioid/monoid definitions (reuse layer)

STEP 0 prior-art: tree already has the [FrdI] Definition 1.1(i)-(ii) divisorial monoid
interface `Iut.DivisorialMonoidOn` (LeanFormal/IUT/IUTII/Frobenioid/DivisorialMonoid
MinimalReplacement.lean:304-320 single-fibre inhabitant; FrobenioidPresentation in
LeanFormal/IUT/Foundations/SourceModelFrobenioidPresentation and used by
Theta/ConcreteSourceEtaleThetaBridge:86).  Ported/FLT assets not needed.

CORPUS: Mochizuki, 'Frobenioids I' ([FrdI]) and 'Frobenioids II' ([FrdII]).

LABEL: class-D definitions reuse layer; the tree definitions are real (not toy); no
paper theorem is claimed here.  Statement rows flagged proved:=false. -/

namespace LeanFormal.IUT.XiFPaper.IUTExternalFrdDefsActual

open LeanFormal.IUT

/- The tree divisorial-monoid interface ([FrdI], Definition 1.1(i)-(ii)). -/
#check @Iut.DivisorialMonoidOn

/- The tree Frobenioid presentation carrier ([FrdI], Definition 1.1 / Definition 1.2 shape). -/
#check @Iut.FrobenioidPresentation

structure IUTExternalFrdRow where
  item : String
  corpus : String
  status : String
  proved : Bool

def iutExternalFrdStatements : List IUTExternalFrdRow :=
  [ ⟨"divisorial monoid definition / functoriality", "[FrdI] Def 1.1(i)-(ii)", "REUSE tree def Iut.DivisorialMonoidOn (single-fibre inhabitant proved)", false⟩,
    ⟨"Frobenioid definition (divisor + Frobenius structure)", "[FrdI] Def 1.1(v)-(vi)", "STATEMENT (class D): tree FrobenioidPresentation is a presentation carrier, full Frobenioid structure not built", false⟩,
    ⟨"Frobenioid morphism / equivalence", "[FrdI] §2", "STATEMENT (class D)", false⟩,
    ⟨"Frobenioid-theoretic interpretation of theta data", "[FrdII] §1", "STATEMENT (class D)", false⟩,
    ⟨"log-Frobenius compatibility", "[FrdII] §2", "STATEMENT (class D)", false⟩ ]

theorem iutExternalFrdStatements_length : iutExternalFrdStatements.length = 5 := rfl

#check iutExternalFrdStatements_length

end LeanFormal.IUT.XiFPaper.IUTExternalFrdDefsActual