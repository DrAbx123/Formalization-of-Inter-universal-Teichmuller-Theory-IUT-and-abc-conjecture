# S2057: actual root-stack Theta-pilot object on q[2u]

Date: 2026-11-02 (Asia/Shanghai). Status: **Lean EXIT=0**.  The finite actual
root-stack Theta-pilot object on the hodgeTwoLthRoot carrier is constructed and
connected to the S2040 displacement/thetaLink.  The **paper** O^tri(T_X)
root-stack carrier is not constructed; the exact first missing and a no-go are
recorded below.  No completion root, no fake stack, no sorry/axiom.

## Lean file

- Source: tmp/sheaf/xif/paper/S2057RootStackThetaPilotActual.lean
- 430 lines, 22542 bytes.
- SHA256: 94FCEDA831CBC13D0A69CB2FB4C79C7C4C97F74BC0FDF095806846C04AD1224D
- Build: lake env lean -j1 -R D:\lean -o
  .lake/build/lib/lean/tmp/sheaf/xif/paper/S2057RootStackThetaPilotActual.olean
  tmp/sheaf/xif/paper/S2057RootStackThetaPilotActual.lean
- EXIT=0; log tmp/sheaf/xif/paper/_S2057_build.log.
- Olean: 1735384 bytes, SHA256
  E5C7F8DBE0B22062A04A646F6AF386A1E51CA555CF1562C6238AB84BB72C8070.
- Consumer: tmp/sheaf/xif/paper/_S2057Consumer.lean, EXIT=0.
- Axioms: every probed declaration depends only on
  [propext, Classical.choice, Quot.sound]; no sorryAx.

## Constructed unconditionally

1. **Actual finite root-stack extension.**  S782/S798's finite extension
   L(mu_{2l}) and the q/root sections stackQSection, stackRootSection are
   reused; the root is the actual 2l-th root, not a completion root.
2. **Root stack groupoid.**  KummerRootStack is Mathlib
   ActionCategory (mu_{2l}) (roots of qSection).  It is a genuine groupoid
   (instance kummerRootStackGroupoid), with the distinguished object
   q2u = rootStackPoint (the actual root section).  It is not the degenerate
   S355 set quotient and not a completion object.
3. **Theta-pilot object.**  S2057RootStackThetaPilotObject carries q2u, root,
   qSection, rootStackTheta, thetaValue j = q[2u]^(j^2), the primitive mu unit,
   the norm law, and the divisor law order/(2l) * j^2.  The inhabitant
   s2057RootStackThetaPilotObject is constructed unconditionally.
4. **hodgeTwoLthRoot identification.**  sourceRoot_eq_hodgeTwoLthRoot proves
   the finite root is definitionally hodgeTwoLthRoot; rootStackPoint is its
   image in the finite root-stack extension.
5. **S2040 displacement.**  Given the paper O^x/O^xmu/ambient data and the
   paper q identification Opaper.q = ||q[1u]||, s2057Displacement constructs an
   actual S2040ThetaLinkDisplacement whose rootStackTheta is the actual root
   norm and whose rootStackTheta_eq uses s2040Theta; s2057ThetaLink_generator
   proves the S2040 thetaLink generator law for the constructed displacement.
6. **Paper 3.12 from first missing.**  s2057ThetaLink312_of_firstMissing builds
   S2040ThetaLink312 with the actual link I.linkAt 0 0 1 0 and derives
   s2057_inclusion_of_firstMissing and s2057_paper312_of_firstMissing.

## Exact first missing (no inhabitant asserted)

- The actual paper O^tri(T_X) root-stack carrier of IUT I Example 3.2(iv).
  What exists in the tree is only the S346 spec
  OrbifoldStructuralSheafCarrierSpec; it is recorded as the paperCarrier field
  of S2057FirstMissing, not inhabited.
- The paper q identification Opaper.q = paperQNorm (the normalized norm of the
  actual q[1u]).  In particular the repo qVFamily cannot be silently used as
  the paper q_v: S342 gives no completion 2l-th root, and the no-go below makes
  this precise.
- The paper O^x / O^xmu / ambient-value data (S1967/S2035): S2035 constructs
  actual local O^x and O^xmu at a completion QPlace, but its Aut-action datum
  is missing and the attachment to the S1895 source input is S1967's exact
  missing.  This is the unitsAmbient field, not inhabited.
- The q-pilot log identification and the paper hull normalization
  P.signedHullLogVolume = log rootStackTheta.

## No-go for the repo q

S2057PaperRootStackCarrierSpec is the shape of a paper O^tri carrier over the
repo q: a monoid carrier with q[1u]/q[2u] sections and a monoid hom
eval : carrier -> Completion which sends q[1u] to the actual qVFamily q.
s2057_paperRootStackCarrier_impossible proves this is empty: the root section
would give a completion TwoLthRootData, contradicting S342.  Therefore the
actual paper root-stack object requires the paper q_v (with 2l | order) and its
O^tri carrier, not the repo qVFamily.  This is a source-object missing, not a
proof gap about the finite root stack.

## Honest boundaries

- The finite root-stack object is an actual algebraic model, but it is not
  claimed to be the paper O^tri(T_X) carrier.
- No completion root, no L substitution, no S355 quotient, no reduced surrogate.
- S1965/S2032 are used as context for the actual local O/O^x carriers in the
  report; the Lean file imports S798, S201, S2040ActualThetaLink312, S346 and
  S342 (the S2032 local Q_p model is not forced onto the number-field source).
- Full Project build, target comparator, and independent review were not run.
