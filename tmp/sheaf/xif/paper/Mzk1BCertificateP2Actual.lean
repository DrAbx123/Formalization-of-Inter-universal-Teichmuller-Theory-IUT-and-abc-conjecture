/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1BCertificateP1Actual
import Mathlib.Tactic

/-! # A990 P2: m_f = min |P(f)| (killed others) and r_f divides m_f -/

/- Model: P has integral coefficients, vanishes on all other eigenforms, and
P(f) = c f with c a nonzero integer. The certificate index r_f divides c (P1).
m_f is the minimum of |P| over the forms killed by P, hence a multiple of c by the
SNF/integer-kernel form. The SNF input c | m_f is an explicit class-B field. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1BCertificateP2Actual

open LeanFormal.IUT.XiFPaper.Mzk1BCertificateP1Actual

/-- SNF integer-kernel package for m_f. -/
structure MinKilledValueData where
  r : Int
  c : Int
  mf : Int
  mf_pos : 0 < mf
  rf_dvd_c : DvdInt r c
  c_dvd_mf : DvdInt c mf

/-- P2: r_f divides m_f (transitivity). -/
theorem rf_dvd_mf (D : MinKilledValueData) : DvdInt D.r D.mf :=
  dvdInt_trans D.rf_dvd_c D.c_dvd_mf

def p2Rows : List (String × String) :=
  [ ("m_f", "min |P| on killed forms (integer kernel gcd form)") ,
    ("c | m_f", "SNF input (class-B field)") ,
    ("r_f | c", "P1 certificate") ,
    ("rf_dvd_mf", "r_f | m_f (PROVED by transitivity)") ]

theorem p2Rows_length : p2Rows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1BCertificateP2Actual
