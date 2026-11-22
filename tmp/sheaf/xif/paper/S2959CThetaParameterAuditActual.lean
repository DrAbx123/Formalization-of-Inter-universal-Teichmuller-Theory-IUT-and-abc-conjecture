/-
# S2959 CThetaPaper parameter audit (actual)

Audit question: does the tree contain actual definitions of the six paper
parameters of

  CThetaPaper l logQ dmod dFpd fFpd eStar etaPrm

bound to the A6/source data, together with an identification with the S2958
half-IQ-hull certificate

  (S2958HalfIQHullCertificateAt a b c habc).thetaSigned ?

Answer at audit time (2026-11-07, ~18:20 +08:00): NO.

## 1. What exists

* S2691ExactQNormalizationActual defines the printed formula CTheta and the
  bracket cThetaBracket, with all six parameters as free Real binders.
* S2715CThetaPaperScaleActual defines CThetaPaper from the same six free
  binders.  S2715 also contains the paper-scale consumer lemmas.
* S2717Cor312FullTargetActual.S2717UpperGap, S2947ThetaUpperEstimateStatement.
  S2947ThetaUpperEstimate, and S2951ThetaSignedActual.S2951ThetaUpperTarget are
  *statements* whose six parameters are universally quantified.  They do not
  define any of them.
* S2953CThetaFromCertificateActual.S2953CThetaUpperCertificate has hCTheta as a
  *field* (a hypothesis), and S2956CThetaPaperUpperActual derives
  CThetaPaper = thetaSigned / |log q| from that field.  S2985SignedThetaCTheta
  Actual likewise stores hCTheta as a field.  A field is not a source
  construction.
* S2807ThetaHullVolumeIdentityActual and S2807SG3a/SG3b transport the same six
  free parameters; they do not define them either.

A grep for def/abbrev declarations whose names contain dmod, dFpd, fFpd, eStar,
etaPrm, or logQ finds no definition of any of the six paper parameters.  The
only parameter-like definitions are S2959HalfIQHullCThetaUpperActual.
S2959ActualDFpd (a fit, see below) and the concurrent S2990ActualDFpdActual.
S2990DFpd/S2990FFpd (see section 4).

## 2. The S2958 certificate is a shifted hull volume

The certificate is tautological (proved below):

  qSigned = -1,
  thetaSigned = hull.hullVolume + 1 = iqHullRealVolume (S2958WAt a b c) + 1,
  1 <= thetaSigned.

There is no theorem relating iqHullRealVolume (S2958WAt a b c), or
S2781LogShellPoint, to the A6 arithmetic datum S2847A6, nor to the six paper
parameters.  S2781LogShellPoint is built from S2752J l a b c (the ABC support
ideal) and the fixed Gaussian q-pilot, not from A6.

## 3. The equality does not determine the six parameters

For every target value theta and every dmod with 1 + 12*dmod/5 > 0 there is a
positive dFpd (with logQ = 1, fFpd = 1, eStar = 0, etaPrm = 0) such that
CThetaPaper = theta.  Hence:

  CThetaPaper S2958l 1 dmod dFpd 1 0 0 = thetaSigned

is not a source identification; it is one scalar equation in six unknowns.
The existing S2959ActualDFpd is the unique positive solution *after fixing the
other five parameters* (see S2959Audit_actualDFpd_is_forced).  It is a parameter
fit, not the paper's dF_tpd.

## 4. A6 and the concurrent dFpd/fFpd candidates

S2847A6 : InitialThetaArithmeticData S2771FiveLabel exists with
Fmod = F = F6 = Q(i, E[6]).  The degree [Fmod : Q] is definable (recorded below
as S2959AuditA6FmodDegree), but it is a closed constant, not a per-ABC-triple
dmod, and no declaration in the tree projects the paper parameters from it.

Observed at 2026-11-07T18:04:38+08:00 (SHA-256
9FE5E664ACCCD2B984ADDD5A828EE15A840541217E9F681A725827C73BCFF951),
S2990ActualDFpdActual.lean defines

  S2990DFpd : Real
    = |differentIdeal Z (SourceOK (A := S2735Arithmetic S2771FiveLabel))|,
  S2990FFpd (a b c) : Real
    = |S2752J S2771FiveLabel a b c|.

These are not the paper's dF_tpd / fF_tpd: S2735Arithmetic has Fmod = F = K = Q(i)
(not the paper's tripodal field F_tpd), and S2752J is the ABC support ideal,
not the conductor.  The file defines no dmod, eStar, etaPrm, or logQ, and proves
no relation of S2990DFpd or S2990FFpd to CThetaPaper or to the S2958
certificate.  It is therefore not the missing source binding.  It is not
imported here, so this audit olean does not depend on a file under active edit.

## 5. Precise missing declarations (proposed names; none exists today)

  S2959LogQAt    (a b c : Nat) : Real  -- paper log q = deg(q^F_ADiv)
  S2959DmodAt    (a b c : Nat) : Real  -- paper d_mod = [F_mod : Q]
  S2959DFpdAt    (a b c : Nat) : Real  -- positive dF_tpd, log = deg(dF_tpd)
  S2959FFpdAt    (a b c : Nat) : Real  -- positive fF_tpd, log = deg(fF_tpd)
  S2959EStarAt   (a b c : Nat) : Real  -- paper e*_mod
  S2959EtaPrmAt  (a b c : Nat) : Real  -- paper eta_prm
  S2959CThetaPaper_source_eq (a b c habc) :
    CThetaPaper S2958l (S2959LogQAt a b c) (S2959DmodAt a b c)
      (S2959DFpdAt a b c) (S2959FFpdAt a b c) (S2959EStarAt a b c)
      (S2959EtaPrmAt a b c) =
    (S2958HalfIQHullCertificateAt a b c habc).thetaSigned

## 6. First error (autoImplicit disabled, literal binding attempt)

  <stdin>:12:24: error(lean.unknownIdentifier): Unknown identifier
  `S2959LogQAt`

The full statement also reports the other five names as unknown identifiers.
This audit file keeps those names as strings and as a hypothesis structure; it
does not fake values for them.

## 7. What a real binding must supply

S2959AuditCThetaPaperSourceBinding packages exactly the missing data: six Reals
plus the equality to the S2958 thetaSigned.  The conditional theorem
S2959Audit_conclusions_of_sourceBinding shows that such a binding would give the
two S2959 conclusions.  The audit finding is that no inhabitant built from
A6/source exists in the tree.
-/

import tmp.sheaf.xif.paper.S2959HalfIQHullCThetaUpperActual
import tmp.sheaf.xif.paper.S2958HalfIQHullCertificateActual
import tmp.sheaf.xif.paper.S2833S2800HregionActual
import tmp.sheaf.xif.paper.S2956CThetaPaperUpperActual
import tmp.sheaf.xif.paper.S2847A6ArithmeticActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2958HalfIQHullCertificateActual
open LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual
open LeanFormal.IUT.XiFPaper.S2691ExactQNormalizationActual
open LeanFormal.IUT.XiFPaper.S2833S2800HregionActual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
open LeanFormal.IUT.XiFPaper.S2959HalfIQHullCThetaUpperActual
open LeanFormal.IUT.XiFPaper.S2953CThetaFromCertificateActual
open LeanFormal.IUT.XiFPaper.S2956CThetaPaperUpperActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2959CThetaParameterAuditActual

/-- The six real arguments of CThetaPaper. -/
structure S2959AuditPaperCThetaArgs where
  logQ : Real
  dmod : Real
  dFpd : Real
  fFpd : Real
  eStar : Real
  etaPrm : Real

/-- The CThetaPaper value of a parameter tuple. -/
noncomputable def S2959AuditPaperCThetaArgs.value
    (P : S2959AuditPaperCThetaArgs) : Real :=
  CThetaPaper S2958l P.logQ P.dmod P.dFpd P.fFpd P.eStar P.etaPrm

/-- Producers audited: all keep the six parameters universally quantified. -/
def S2959AuditFreeParameterConsumers : List String :=
  [ "S2691ExactQNormalizationActual.CTheta/cThetaBracket (six binders)"
  , "S2715CThetaPaperScaleActual.CThetaPaper (six binders)"
  , "S2717Cor312FullTargetActual.S2717UpperGap/PaperCor312Full"
  , "S2947ThetaUpperEstimateStatement.S2947ThetaUpperEstimate"
  , "S2951ThetaSignedActual.S2951ThetaUpperTarget"
  , "S2953CThetaFromCertificateActual.S2953CThetaUpperCertificate.hCTheta (field)"
  , "S2956CThetaPaperUpperActual.S2956_CThetaPaper_eq_thetaSigned_div (from field)"
  , "S2807ThetaHullVolumeIdentityActual.S2807_paperCor312Full_iff_haarRegion"
  , "S2985SignedThetaCThetaActual.S2985SignedThetaCarrier.hCTheta (field)"
  , "S2959HalfIQHullCThetaUpperActual.S2959ActualDFpd (fit, not source)"
  ]

/-- The precise source declarations that are absent (proposed names). -/
def S2959AuditMissingSourceDeclarations : List String :=
  [ "S2959LogQAt (a b c : Nat) : Real -- paper log q = deg(q^F_ADiv)"
  , "S2959DmodAt (a b c : Nat) : Real -- paper d_mod = [F_mod : Q]"
  , "S2959DFpdAt (a b c : Nat) : Real -- positive dF_tpd, log = deg(dF_tpd)"
  , "S2959FFpdAt (a b c : Nat) : Real -- positive fF_tpd, log = deg(fF_tpd)"
  , "S2959EStarAt (a b c : Nat) : Real -- paper e*_mod"
  , "S2959EtaPrmAt (a b c : Nat) : Real -- paper eta_prm"
  , "S2959CThetaPaper_source_eq (a b c habc) -- the six above equal thetaSigned"
  ]

/-- First error of the literal source-binding statement, with
autoImplicit disabled: Lean does not know the first missing name. -/
def S2959AuditFirstError : String :=
  "error: unknown identifier 'S2959LogQAt'"

/-! ## 1. The S2958 certificate is a shifted hull volume -/

theorem S2959Audit_certificate_qSigned (a b c : Nat) (habc : IsABCTriple a b c) :
    (S2958HalfIQHullCertificateAt a b c habc).qSigned = -1 := rfl

theorem S2959Audit_certificate_thetaSigned_eq_hullVolume_add_one
    (a b c : Nat) (habc : IsABCTriple a b c) :
    (S2958HalfIQHullCertificateAt a b c habc).thetaSigned =
      (S2958HalfIQHullCertificateAt a b c habc).hull.hullVolume + 1 := rfl

theorem S2959Audit_certificate_thetaSigned_eq_iqHullRealVolume_add_one
    (a b c : Nat) (habc : IsABCTriple a b c) :
    (S2958HalfIQHullCertificateAt a b c habc).thetaSigned =
      iqHullRealVolume (S2958WAt a b c) + 1 := rfl

theorem S2959Audit_certificate_one_le_thetaSigned
    (a b c : Nat) (habc : IsABCTriple a b c) :
    1 <= (S2958HalfIQHullCertificateAt a b c habc).thetaSigned := by
  rw [S2959Audit_certificate_thetaSigned_eq_iqHullRealVolume_add_one]
  linarith [iqHullRealVolume_nonneg (S2958WAt a b c)]

theorem S2959Audit_certificate_trivial_inclusion
    (a b c : Nat) (habc : IsABCTriple a b c) :
    -1 <= (S2958HalfIQHullCertificateAt a b c habc).hull.hullVolume := by
  have h := (S2958HalfIQHullCertificateAt a b c habc).q_le_hull
  have hq : (S2958HalfIQHullCertificateAt a b c habc).qSigned = -1 := rfl
  rwa [hq] at h

/-! ## 2. The equality does not determine the six paper parameters -/

/-- For any target theta and any dmod with positive bracket coefficient there
is a positive dFpd (with logQ = 1, fFpd = 1, eStar = 0, etaPrm = 0) fitting it. -/
theorem S2959Audit_CThetaPaper_at_chosen_dFpd
    (theta dmod : Real) (hc : 0 < 1 + 12 * dmod / 5) :
    CThetaPaper S2958l 1 dmod
      (Real.exp ((theta + 23 / 10) / (15 * (1 + 12 * dmod / 5)))) 1 0 0 = theta := by
  have h5 : (0 : Real) < 5 + 12 * dmod := by linarith
  unfold CThetaPaper cThetaBracket
  rw [Real.log_exp, Real.log_one]
  unfold S2958l S2833l fiveLabel paperQAbsLog qNormFactor
  norm_num
  field_simp [ne_of_gt h5]
  ring

theorem S2959Audit_exists_positive_dFpd
    (theta dmod : Real) (hc : 0 < 1 + 12 * dmod / 5) :
    exists dFpd : Real, 0 < dFpd ∧
      CThetaPaper S2958l 1 dmod dFpd 1 0 0 = theta := by
  exact ⟨Real.exp ((theta + 23 / 10) / (15 * (1 + 12 * dmod / 5))),
    Real.exp_pos _, S2959Audit_CThetaPaper_at_chosen_dFpd theta dmod hc⟩

/-- Two different dmod values (hence two different parameter tuples) realize the
same target theta.  So the equality to thetaSigned cannot identify the source
parameters. -/
theorem S2959Audit_parameters_not_determined (theta : Real) :
    exists dmod1 dmod2 dFpd1 dFpd2 : Real,
      dmod1 ≠ dmod2 ∧ 0 < dFpd1 ∧ 0 < dFpd2 ∧
      CThetaPaper S2958l 1 dmod1 dFpd1 1 0 0 = theta ∧
      CThetaPaper S2958l 1 dmod2 dFpd2 1 0 0 = theta := by
  obtain ⟨d1, hd1, h1⟩ := S2959Audit_exists_positive_dFpd theta 0 (by norm_num)
  obtain ⟨d2, hd2, h2⟩ := S2959Audit_exists_positive_dFpd theta 5 (by norm_num)
  exact ⟨0, 5, d1, d2, by norm_num, hd1, hd2, h1, h2⟩

/-! ## 3. The existing fit S2959ActualDFpd is forced, not source-derived -/

theorem S2959Audit_actualDFpd_eq_exp
    (a b c : Nat) (habc : IsABCTriple a b c) :
    S2959ActualDFpd a b c habc =
      Real.exp (((S2958HalfIQHullCertificateAt a b c habc).thetaSigned + 23 / 10) / 15) := by
  unfold S2959ActualDFpd
  congr 1
  ring

/-- With the other five parameters fixed as in the S2959 fit, the equality forces
the positive dFpd. -/
theorem S2959Audit_dFpd_unique_of_equality
    (theta dFpd : Real) (hd : 0 < dFpd) :
    CThetaPaper S2958l 1 0 dFpd 1 0 0 = theta ↔
      dFpd = Real.exp ((theta + 23 / 10) / 15) := by
  constructor
  · intro h
    have hlog : Real.log dFpd = (theta + 23 / 10) / 15 := by
      have h' := h
      unfold CThetaPaper cThetaBracket at h'
      rw [Real.log_one] at h'
      unfold S2958l S2833l fiveLabel paperQAbsLog qNormFactor at h'
      norm_num at h'
      linarith
    rw [← hlog, Real.exp_log hd]
  · intro h
    rw [h]
    have h := S2959Audit_CThetaPaper_at_chosen_dFpd theta 0
      (by norm_num : (0 : Real) < 1 + 12 * 0 / 5)
    simpa using h

/-- The S2959ActualDFpd equality is the unique positive solution of the scalar
equation once the other five parameters are fixed; it is a fit. -/
theorem S2959Audit_actualDFpd_is_forced
    (a b c : Nat) (habc : IsABCTriple a b c) :
    CThetaPaper S2958l 1 0 (S2959ActualDFpd a b c habc) 1 0 0 =
        (S2958HalfIQHullCertificateAt a b c habc).thetaSigned ∧
      ∀ dFpd : Real, 0 < dFpd →
        CThetaPaper S2958l 1 0 dFpd 1 0 0 =
          (S2958HalfIQHullCertificateAt a b c habc).thetaSigned →
        dFpd = S2959ActualDFpd a b c habc := by
  constructor
  · exact S2959_CThetaPaper_eq_theta_signed a b c habc
  · intro dFpd hd h
    rw [S2959Audit_actualDFpd_eq_exp]
    exact (S2959Audit_dFpd_unique_of_equality _ _ hd).mp h

/-! ## 4. What a real source binding has to supply -/

/-- The missing source binding: six paper parameters plus the equality to the
S2958 certificate.  No inhabitant built from A6/source exists in the tree. -/
structure S2959AuditCThetaPaperSourceBinding
    (a b c : Nat) (habc : IsABCTriple a b c) where
  logQ : Real
  dmod : Real
  dFpd : Real
  fFpd : Real
  eStar : Real
  etaPrm : Real
  hC : CThetaPaper S2958l logQ dmod dFpd fFpd eStar etaPrm =
    (S2958HalfIQHullCertificateAt a b c habc).thetaSigned

/-- Conditional bridge: a source binding would give the two S2959 conclusions. -/
theorem S2959Audit_conclusions_of_sourceBinding
    {a b c : Nat} {habc : IsABCTriple a b c}
    (B : S2959AuditCThetaPaperSourceBinding a b c habc) :
    (S2958HalfIQHullCertificateAt a b c habc).thetaSigned <=
        CThetaPaper S2958l B.logQ B.dmod B.dFpd B.fFpd B.eStar B.etaPrm *
          |Real.log S2959Q| ∧
      -1 <= CThetaPaper S2958l B.logQ B.dmod B.dFpd B.fFpd B.eStar B.etaPrm := by
  constructor
  · rw [S2959_abs_logQ, mul_one, B.hC]
  · rw [B.hC]
    have hq : (S2958HalfIQHullCertificateAt a b c habc).qSigned = -1 := rfl
    have h := (S2958HalfIQHullCertificateAt a b c habc).q_le_theta
    rwa [hq] at h

/-! ## 5. A6 and the concurrent dFpd candidates -/

#check S2847A6
#check S2847A6.Fmod

/-- The A6 Fmod degree is definable, but it is a closed constant, not a
per-ABC-triple dmod.  Recorded to distinguish 'no declaration' from
'impossible quantity'. -/
noncomputable def S2959AuditA6FmodDegree : Real :=
  (Module.finrank ℚ S2847A6.Fmod : Real)

#check S2959AuditA6FmodDegree
#check S2953CThetaUpperCertificate
#check S2956_CThetaPaper_eq_thetaSigned_div
#check S2959ActualDFpd
#check S2959_CThetaPaper_eq_theta_signed

/-! ## 6. Checks -/

#check S2959AuditPaperCThetaArgs
#check S2959AuditFreeParameterConsumers
#check S2959AuditMissingSourceDeclarations
#check S2959AuditFirstError
#check S2959Audit_certificate_qSigned
#check S2959Audit_certificate_thetaSigned_eq_hullVolume_add_one
#check S2959Audit_certificate_one_le_thetaSigned
#check S2959Audit_certificate_trivial_inclusion
#check S2959Audit_parameters_not_determined
#check S2959Audit_actualDFpd_is_forced
#check S2959AuditCThetaPaperSourceBinding
#check S2959Audit_conclusions_of_sourceBinding

#print axioms S2959Audit_certificate_thetaSigned_eq_hullVolume_add_one
#print axioms S2959Audit_certificate_one_le_thetaSigned
#print axioms S2959Audit_parameters_not_determined
#print axioms S2959Audit_dFpd_unique_of_equality
#print axioms S2959Audit_actualDFpd_is_forced
#print axioms S2959Audit_conclusions_of_sourceBinding

end LeanFormal.IUT.XiFPaper.S2959CThetaParameterAuditActual
