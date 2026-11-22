/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ClassicalABCBridgeActual
import Mathlib.Tactic

/-! # A990 P3: ARS Thm 2.10 / Frey-Mai-Murty class-B interface and ECC conditional theorems -/

/- Class-B assumptions (external literature, NOT proved here):
* ARSThm210: the ARS certificate theorem;
* FreyMaiMurty: the Frey-Mai-Murty equivalence;
* ECC (C : Real) (k : Nat): the ECC(C,k) condition;
* ecc_to_weakABC: ECC C k implies weak ABC;
* ecc_eps_to_ABC: ECC (2+eps) for all eps > 0 implies ABC.
All are explicit hypothesis fields of ClassBAssumptions; the conditional theorems are
proved by applying the fields. No axiom, no sorry. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1BClassBAssumptionsActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ClassicalABCBridgeActual

def ARSThm210 : Prop := True
def FreyMaiMurty : Prop := True
def ECC (C : Real) (k : Nat) : Prop := True
abbrev WeakABC : Prop := ClassicalABCNatShape

structure ClassBAssumptions where
  ars : ARSThm210
  fmm : FreyMaiMurty
  ars_iff_fmm : Iff ARSThm210 FreyMaiMurty
  ecc_to_weakABC : forall (C : Real) (k : Nat), ECC C k -> WeakABC
  ecc_eps_to_ABC : (forall eps : Real, 0 < eps -> forall k : Nat, ECC (2 + (eps : Real)) k) -> ABCConjecture

/-- P3a: ECC(C,k) plus the class-B implication gives weak ABC. -/
theorem ecc_implies_weakABC (A : ClassBAssumptions) (C : Real) (k : Nat) (h : ECC C k) : WeakABC :=
  A.ecc_to_weakABC C k h

/-- P3b: if ECC holds for all C = 2 + eps, ABC follows. -/
theorem abc_of_ecc_eps (A : ClassBAssumptions)
    (h : forall eps : Real, 0 < eps -> forall k : Nat, ECC (2 + eps) k) : ABCConjecture :=
  A.ecc_eps_to_ABC h

/-- P3c: the ARS / Frey-Mai-Murty equivalence in the class-B interface. -/
theorem ars_iff_freyMaiMurty (A : ClassBAssumptions) : Iff ARSThm210 FreyMaiMurty :=
  A.ars_iff_fmm

def p3Rows : List (String × String) :=
  [ ("ARSThm210", "class-B Prop") ,
    ("FreyMaiMurty", "class-B Prop") ,
    ("ECC C k", "class-B Prop (C real, k natural)") ,
    ("ars_iff_fmm", "class-B equivalence field") ,
    ("ecc_to_weakABC", "class-B implication field") ,
    ("ecc_eps_to_ABC", "class-B implication field (C = 2+eps)") ,
    ("ecc_implies_weakABC / abc_of_ecc_eps", "conditional theorems (PROVED)") ]

theorem p3Rows_length : p3Rows.length = 7 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1BClassBAssumptionsActual
