/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # P3 GAP ledger (machine-checked status list; no mathematical claims) -/

namespace LeanFormal.IUT.XiFPaper.Mzk1P3GapLedgerActual

def p3GapRows : List (String × String × String) :=
  [ ("GAP-PC-WEIGHT", "actual local weight = 1", "reduced to FINITE/AGREE/UNRAM-RESIDUE"),
    ("GAP-PC-FINITE", "Module.Finite completed valuation rings", "PROVED via FLT BaseChange priority-1001 instance (FiniteFLT DONE); T arithmetic instances constructed"),
    ("GAP-PC-AGREE", "completed local e/f vs place data", "PROVED via FLT Completion/BaseChange (AgreeFLT DONE); both components closed"),
    ("GAP-PC-UNRAM-RESIDUE", "relative e = f = 1", "iff relative degree one formalized; UnramResidue file pending green; tame derivation GAP"),
    ("GAP-PC-LOGSUM", "log C.p <= sum |log q_b|", "reduced to GAP-PC-RESNORM (LogSum green)"),
    ("GAP-PC-RESNORM", "residueNormBase native = C.p", "reduced to RESDEG + BADCHAR (ResNorm green)"),
    ("GAP-PC-RESDEG", "localResidueDegree native = 1", "equiv to norm equality (ResNormSlack/ResDeg green); tame derivation GAP"),
    ("GAP-PC-BADCHAR", "residueNormBase b.1 = C.p", "reduced to NORMFORMULA/PRIME/DEG (BadChar green)"),
    ("GAP-PC-NORMFORMULA", "residueNormBase = char^inertiaDegree", "PROVED (NormFormulaProof DONE 22:58:24)"),
    ("GAP-PC-BADCHAR-PRIME", "residueCharacteristic b.1 = C.p", "one direction green (BadCharPrime); conductor id GAP"),
    ("GAP-PC-BADCHAR-DEG", "residueInertiaDegree b.1 = 1", "GAP residue degree"),
    ("DICT-B", "paper (D,Q,S,T) vs arithmetic quantities", "DICT-A green; DICT-B/C GAP"),
    ("DICT-C", "box upper bound vs L6 lower bound direction", "one-way only; reverse UNKNOWN"),
    ("external", "MestreOesterleBound", "EXTERNAL PARAM Prop") ]

theorem p3GapRows_length : p3GapRows.length = 14 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P3GapLedgerActual
