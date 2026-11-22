import LeanFormal.IUT.Audit.Status

/-! # S3131 dependency-map wording update: [GenEll] exact role (data only) -/

namespace LeanFormal.IUT.XiFPaper.S3131GenEllDependencyUpdateActual

def S3131GenEllDependencyUpdate : List (String × String) :=
  [ ("old vague label", "'GenEll-strength' (retired)"),
    ("exact reference", "[GenEll] = Mochizuki, Arithmetic Elliptic Curves in General Position, Math. J. Okayama Univ. 52 (2010) 1-28; corpus in papers/motizuki_corpus; IUT IV biblio line 4505"),
    ("[GenEll] Theorem 2.1", "EQUIVALENCE (general case <=> compactly bounded case); it is a REDUCTION theorem, not a proof of ABC and not the bound itself"),
    ("paper-route field (c)", "IUT-side height/volume bound (IUT IV Thm 1.10 shape / IV section 2 estimates) = split point bound + unit-region bound (Cor312 Gap 2); GenEll converts compactly-bounded to general on top of it"),
    ("consequence", "(c) remains a genuine bound obligation; GenEll labeled precisely and cited rather than invoked as strength") ]

theorem S3131GenEllDependencyUpdate_length : S3131GenEllDependencyUpdate.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.S3131GenEllDependencyUpdateActual