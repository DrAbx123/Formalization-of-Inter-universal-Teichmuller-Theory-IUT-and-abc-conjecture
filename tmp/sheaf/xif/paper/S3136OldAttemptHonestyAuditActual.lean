/-! # Stage-4 host: honesty audit of the old-attempt (c) wiring (§7.9 mining)

PRIOR ART MINED (checked first): S2586IQHullLogVolumeInstantiationActual (concrete IQ
interface over native Haar), S2588RationalPointMapActual (point map), S2590PadicSingletonNullActual
(singleton-null), S2595UnconditionalDictionaryActual (S2595Dictionary/S2595_hpoint),
S2720BridgeHaarActual:70 (split lemma), S2722HunitDActual:34/44/68 (D0/hunitD/gap2),
S2722HpointActual:30 (hpoint), S2722Gap2AssemblyActual:35/58 (epsilonComparison/bridge).

AUDIT FLAGS (binding for all consumers; no discharge claims):
1. The old attempt's final `S2722_bridgeS2586` produces a `Cor312ToABCBridgeInterface`
   from two named inputs hval (uniform valuation bound) and hweightvol (gap-1
   dictionary direction).  That interface is the ABC-STRENGTH calibration interface
   (Nonempty <-> ABCConjecture per the audit); a conditional inhabitant is a
   conditional ABC-strength statement, NOT progress toward a proof.
2. hval (uniform valuation bound) is the input that the prior art records as REFUTED
   (Cor312GapDictionaryLayer header: the refuted uniform valuation bound is replaced
   by the approved additive input).  It must not be assumed.
3. hweightvol (arithmeticWeight <= normalizedComparisonRegion.logVolume) is exactly
   the gap-1 dictionary direction and remains OPEN (the dictionary layer proves
   maximal fragments and non-universality, not the universal direction).
4. The old attempt discharges hpoint via singleton-null: singleton subsets have
   Haar log-volume 0, so the point bound is vacuous/degenerate.  The paper's point
   log-volume is NOT zero; this is a measure-carrier artifact, not the paper's
   point-height comparison.
5. `S2595Dictionary`/`S2595_hpoint` are unconditional only within this degenerate
   singleton-null carrier; they do not transfer to the paper's carrier.

LABEL: audit honesty record (data). Registry frozen; new file only. -/

namespace LeanFormal.IUT.XiFPaper.S3136OldAttemptHonestyAuditActual

structure LGPOldAttemptAuditRow where
  item : String
  finding : String
  consequence : String

def lgpOldAttemptAudit : List LGPOldAttemptAuditRow :=
  [ ⟨"S2722_bridgeS2586", "produces Cor312ToABCBridgeInterface from hval + hweightvol", "ABC-STRENGTH conditional; not progress/discharge"⟩,
    ⟨"hval (uniform valuation bound)", "recorded REFUTED in Cor312GapDictionaryLayer header", "must not be assumed; use additive input instead"⟩,
    ⟨"hweightvol (gap-1 dictionary direction)", "open: universal arithmeticWeight <= region volume not proved", "named open input, not evidence"⟩,
    ⟨"hpoint via S2590SingletonNull", "degenerate: Haar singletons are null so point volume = 0", "point bound not the paper's point-height comparison"⟩,
    ⟨"S2595Dictionary/S2595_hpoint", "unconditional only on the degenerate singleton-null carrier", "does not transfer to the paper carrier"⟩,
    ⟨"hunit (S2722_hunitD)", "GENUINE measure fact with actual D0 = max 0 (unitVol - hullVol)", "reusable as the unit-region bound on the S2586 carrier"⟩,
    ⟨"hsplit (S2720BridgeHaarActual:70)", "GENUINE per-triple subadditivity for the S2586 carrier", "reusable as the split-point bound shape"⟩,
    ⟨"hptfin (singleton-null)", "GENUINE finiteness on the S2586 carrier", "reusable, but note degeneracy of point volume"⟩ ]

theorem lgpOldAttemptAudit_length : lgpOldAttemptAudit.length = 8 := rfl

#check lgpOldAttemptAudit
#check lgpOldAttemptAudit_length

end LeanFormal.IUT.XiFPaper.S3136OldAttemptHonestyAuditActual