import tmp.sheaf.xif.paper.S1991HonestTargetAliasesActual

/-! Import check for the S1991 olean. -/

open LeanFormal.IUT.XiFPaper.S1991HonestTargetAliasesActual

#check S1991HonestCFSignature
#check S1991HonestCFSignature_eq_S1964HonestQuotientSignature
#check S1991HonestCFQuotientAt
#check S1991LegacyCFQuotientAt
#check S1991HonestCFQuotient
#check S1991LegacyCFQuotient
#check S1991HonestPaperCF
#check S1991LegacyPaperCF
#check S1991HonestCFQuotientAt_nonempty_iff_legacy
#check S1991HonestCFQuotient_nonempty_iff_legacy
#check S1991HonestPaperCF_nonempty_iff_legacy
#check S1991FirstMissing
#check S1991PaperFirstMissing
#check S1991FirstMissing_iff_S1964FirstMissing
#check S1991FirstMissing_iff_S1983FirstMissing
#check S1991HonestSignatureNotForcedByFiber
#check S1991TargetLockDecision

#print axioms S1991TargetLockDecision
