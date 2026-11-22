# S1991: corrected honest target aliases (actual)

Date: 2026-11-01 (Asia/Shanghai)
Workspace: D:\lean
Source: tmp/sheaf/xif/paper/S1991HonestTargetAliasesActual.lean
OLean: .lake/build/lib/lean/tmp/sheaf/xif/paper/S1991HonestTargetAliasesActual.olean
Status: EXIT=0. Production definitions unchanged. No axiom, sorry, admit or
arbitrary carrier. The exact first missing is G1.

## Verification

- Build: lake env lean -j1 -R D:\lean -o <olean> <source>, EXIT=0.
- Log: tmp/sheaf/xif/paper/S1991_compile.log
  - 0 errors, 0 warnings, 0 sorryAx.
  - 39 #print axioms blocks; only propext, Classical.choice, Quot.sound.
- Import check: tmp/sheaf/xif/paper/_S1991OleanCheck.lean
  - log tmp/sheaf/xif/paper/S1991_olean_check.log, CHECK_EXIT=0.
- Source:
  - 27107 bytes, 616 lines, 28 theorems, 13 defs, 7 abbrevs, 3 structures.
  - SHA256 2A7BF11975250D0D0D7AA3E256A97281ED41039B8E41FFA8E0B77DDF132804CE
- OLean:
  - 266616 bytes
  - SHA256 53A4F2DE09C78FFF9A23712A05792CF76BDDB71AA375BE2A5721BE326838AC82
- Compile log SHA256 ADB330E714E350B43F8E295E1B4E9D1928341156085ADC2BB8DFC677D85986D4
- Import-check log SHA256 DE15BD97C0F409DCB67C976A12A41998112A1D384BF5A08407C01CD11A7E5806
- The only source occurrence of the word sorry is the honesty paragraph line 48
  ("No axiom, sorry, admit or arbitrary carrier is introduced"); there is no
  sorry tactic and no axiom declaration.

## The corrected signature

S1991HonestCFSignature := etthSignature EtThType.oneOnePlusMinus

Machine-checked:

* S1991HonestCFSignature = S1964HonestQuotientSignature
  (S1991HonestCFSignature_eq_S1964HonestQuotientSignature)
* S1991HonestCFSignature = (0; [2,2,2]; 1), literally
  (S1991HonestCFSignature_eq_literal, S1991HonestCFSignature_data)
* chi = -1/2 (S1991HonestCFSignature_euler), hyperbolic
  (S1991HonestCFSignature_hyperbolic)
* S1991HonestCFSignature != sourceTypeOneOnePlusMinus = (1; [2]; 0)
  (S1991HonestCFSignature_ne_legacy); the two labels differ in genus,
  stacky orders and punctures (S1991HonestCFSignature_vs_legacy)
* the Euler characteristic cannot detect the error: both labels have
  chi = -1/2 (S1991HonestCFSignature_euler_eq_legacy)

## Corrected target aliases, side by side with the legacy labels

S1964 layer:

* S1991HonestCFQuotientAt l A :=
    S1964CFQuotientAt l A S1991HonestCFSignature _
* S1991LegacyCFQuotientAt l A :=
    S1964CFQuotientAt l A sourceTypeOneOnePlusMinus _
  The honest alias is definitionally S1983EtThCF and S1964HonestCFQuotient.

S1932 layer:

* structure S1991HonestCFQuotient l A: cF, cF_signature = honest, quotient,
  quotientWitness (the same four fields as S1932CFQuotient, corrected label)
* S1991LegacyCFQuotient l A := S1932CFQuotient l A

S1886 layer:

* structure S1991HonestPaperCF l: action, cF, cF_signature = honest, quotient,
  quotientWitness (the same five fields as S1886PaperCF, corrected label)
* S1991LegacyPaperCF l := S1886PaperCF l

## The relabelling bridge

S1991Relabel changes only the stored signature on the same etale-stack fiber
(realizedHyperbolicOrbicurve applied to the existing fiber).  Since
HyperbolicOrbicurve.Hom and all quotient data only see stack.fiber,
S1991InvariantMorphismRelabel and S1991QuotientWitnessRelabel transport the
quotient morphism and the bicategorical universal property unchanged.
S1991CFQuotientAtChangeLabel then changes the label of any parameterized
target.

Machine-checked equivalences:

* any two hyperbolic labels of S1964CFQuotientAt have the same inhabitedness
  (S1991CFQuotientAt_nonempty_iff_of_label)
* honest S1964 target <-> legacy S1964 target
  (S1991HonestCFQuotientAt_nonempty_iff_legacy)
* honest S1932 target <-> legacy S1932 target
  (S1991HonestCFQuotient_nonempty_iff_legacy)
* honest S1886 target <-> legacy S1886 target
  (S1991HonestPaperCF_nonempty_iff_legacy)
* honest S1886 target <-> an action A plus the honest S1932 target for A
  (S1991HonestPaperCF_nonempty_iff_exists)
* honest S1886 target <-> an action A plus the legacy S1932 target for A
  (S1991HonestPaperCF_nonempty_iff_legacyExists)
* the summary S1991TargetLockDecision records all of the above in one theorem.

## Exact first missing

For the corrected targets the only missing object is G1:

  S1964FirstMissing l A = Nonempty (S1964QuotientStructure l A),

the quotient stack [X_F/{±1}], its functoriality/stackification, and its
bicategorical universal property.  Machine-checked:

* honest S1964 target <-> S1964FirstMissing
  (S1991HonestCFQuotientAt_nonempty_iff_firstMissing)
* honest S1932 target <-> S1964FirstMissing
  (S1991HonestCFQuotient_nonempty_iff_firstMissing,
   S1991FirstMissing_iff_S1964FirstMissing)
* honest S1932 target <-> S1983FirstMissing
  (S1991FirstMissing_iff_S1983FirstMissing)
* S1991CFQuotientAtOfStructure constructs the honest target from an arbitrary
  label-free quotient structure by relabelling; this is the converse direction
  of the equivalence, not a construction of G1.
* paper-level: honest S1886 target <-> exists A, S1964FirstMissing l A
  (S1991PaperFirstMissing_iff_exists_firstMissing).

G2 is recorded, not hidden:

* S1991HonestSignatureNotForcedByFiber (from S1983): for every etale-stack
  fiber there is a hyperbolic orbicurve on that fiber whose signature is not
  (0; [2,2,2]; 1).  Hence the honest label in the corrected target is target
  data, not a geometric consequence of the fiber.  Forcing it geometrically
  requires changing the production signature field to be computed from the
  quotient geometry; that change is out of scope and is not done here.

## Target-lock decision (M4)

The paper-faithful, additive option is adopted:

* the production structures S1932CFQuotient, S1886PaperCF and
  S1964CFQuotientAt are not retyped and not modified;
* S1991HonestCFQuotient, S1991HonestPaperCF and S1991HonestCFQuotientAt are
  the corrected targets to use for paper-faithful downstream work;
* the legacy aliases remain available for comparison;
* the honest and legacy versions stand or fall together (same inhabitedness);
* the first missing remains G1; G2 is a target-adequacy caveat, not an
  additional unproved inhabitant.

## Not done / not claimed

* No quotient stack, no stackification and no universal-property inhabitant is
  constructed; G1 is still missing.
* No production definition is changed.
* The honest label is not claimed to be computed from the quotient geometry.
* No new axiom, sorry, admit, True/PUnit substitute or arbitrary carrier.

## Files added

* tmp/sheaf/xif/paper/S1991HonestTargetAliasesActual.lean
* .lake/build/lib/lean/tmp/sheaf/xif/paper/S1991HonestTargetAliasesActual.olean
* tmp/sheaf/xif/paper/_S1991OleanCheck.lean
* tmp/sheaf/xif/paper/S1991_compile.log
* tmp/sheaf/xif/paper/S1991_olean_check.log
* tmp/sheaf/xif/paper/S1991_report.md (this file)
