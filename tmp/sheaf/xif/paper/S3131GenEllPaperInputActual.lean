import Mathlib
import LeanFormal.IUT.Audit.Status

/-! # S3131 [GenEll] PAPER-INPUT STATEMENT EXTRACTION (not a proof; exact reference)

Source: S. Mochizuki, 'Arithmetic Elliptic Curves in General Position',
Math. J. Okayama Univ. 52 (2010) 1-28; corpus text:
papers/motizuki_corpus/text/Arithmetic Elliptic Curves in General Position.txt;
IUT IV bibliography line 4505.  Theorem 2.1 (corpus lines 615-687) is an
EQUIVALENCE: (i) ABC/effective Mordell/Vojta for all hyperbolic curves over
number fields  <=>  (ii) ABC for Sigma-supported compactly bounded subsets.
GenEll is a REDUCTION theorem (compactly bounded => general); it does NOT supply
the height/volume bound itself.  Our (c) field is IUT-side (IV Thm 1.10 shape).

This file records the statement SHAPES as paper-input Props (no proofs claimed). -/

namespace LeanFormal.IUT.XiFPaper.S3131GenEllPaperInputActual

/-- BD-class inequality (height <= (1+eps)(log-diff + log-cond)), the shape in
[GenEll] Theorem 2.1 (i)/(ii). -/
def BDInequality (height logDiff logCond : Real) (eps : Real) : Prop :=
  height ≤ (1 + eps) * (logDiff + logCond)

/-- Compactly bounded subset condition (shape): a set of rational points cut out
by the compactly-bounded height condition on K_V cap U_P(Q)<=d. -/
def CompactlyBoundedCut (inSubset : Prop) : Prop := inSubset

/-- [GenEll] Theorem 2.1 EQUIVALENCE shape as an explicit paper-input Prop.
The two sides are kept as abstract Props so the equivalence is a statement,
not a claimed theorem in this file. -/
def GenEllEquivalenceStatement (generalCase compactlyBoundedCase : Prop) : Prop :=
  generalCase ↔ compactlyBoundedCase

/-- The reduction direction actually used: compactly bounded case => general case. -/
def GenEllReductionDirection (generalCase compactlyBoundedCase : Prop) : Prop :=
  compactlyBoundedCase → generalCase

#check BDInequality
#check GenEllEquivalenceStatement
#check GenEllReductionDirection

end LeanFormal.IUT.XiFPaper.S3131GenEllPaperInputActual