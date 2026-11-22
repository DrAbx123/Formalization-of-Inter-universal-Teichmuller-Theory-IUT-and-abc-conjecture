import LeanFormal.IUT.Audit.Status

/-! # S3131 [GenEll] corpus citations (data only) -/

namespace LeanFormal.IUT.XiFPaper.S3131GenEllCorpusCitationsActual

def S3131GenEllCitations : List (String × String) :=
  [ ("papers/motizuki_corpus/text/Arithmetic Elliptic Curves in General Position.txt", "S. Mochizuki, Math. J. Okayama Univ. 52 (2010) 1-28; 66541 B in repo"),
    ("IUT IV bibliography", "line 4505 (verified by Lead)"),
    ("[GenEll] Definition 1.2 / 1.5, Example 1.3, Propositions 1.4 / 1.7", "BD-class height comparisons (cited; exact line extraction pending)"),
    ("[GenEll] Theorem 2.1 (corpus lines 615-687)", "EQUIVALENCE: general ABC/effective Mordell/Vojta <=> Sigma-supported compactly bounded ABC; proof uses noncritical Belyi maps [Mzk1], Elkies technique, Prop 1.4/1.7"),
    ("papers/motizuki_corpus/text/Noncritical Belyi Maps.txt", "[Mzk1] noncritical Belyi maps (17908 B in repo)") ]

theorem S3131GenEllCitations_length : S3131GenEllCitations.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.S3131GenEllCorpusCitationsActual