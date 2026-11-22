import LeanFormal.IUT.Audit.Status

/-! # S3131 [Mzk1] Noncritical Belyi Maps statement schema -/

namespace LeanFormal.IUT.XiFPaper.S3131Mzk1StatementActual

/-- [Mzk1] noncritical Belyi maps existence shape: for a hyperbolic curve and a
finite set of primes/points, there is a noncritical Belyi map controlling bad reduction. -/
def NoncriticalBelyiStatement (existsNoncriticalMap : Prop) : Prop :=
  existsNoncriticalMap

def S3131Mzk1CitationRow : List (String × String) :=
  [ ("[Mzk1]", "papers/motizuki_corpus/text/Noncritical Belyi Maps.txt (17908 B in repo)"),
    ("role", "input to [GenEll] Theorem 2.1 proof (noncritical Belyi maps technique)") ]

theorem S3131Mzk1CitationRow_length : S3131Mzk1CitationRow.length = 2 := rfl

end LeanFormal.IUT.XiFPaper.S3131Mzk1StatementActual