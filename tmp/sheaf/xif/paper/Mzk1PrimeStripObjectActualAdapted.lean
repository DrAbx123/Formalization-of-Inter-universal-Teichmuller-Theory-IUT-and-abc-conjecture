import Mathlib

/-!
# Mzk1PrimeStripObjectActualAdapted (adapted copy, A475 reuse) — prime-strip object (genuine defininitions + projections)

Status: PENDING-VERIFY (watchdog compile). No sorry, no axiom, no fake closure.
Formal model: a prime-strip carries a labelled point with an index label; projections are genuine.
Registers DEF-level object only. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1PrimeStripObjectActualAdapted

/-- A prime-strip: a carrier with an index label. -/
structure PrimeStrip (Index Carrier : Type*) where
  carrier : Carrier
  label : Index

/-- Genuine projection: the carrier of a prime-strip. -/
def PrimeStrip.carrierOf {Index Carrier : Type*} (s : PrimeStrip Index Carrier) : Carrier := s.carrier

/-- Genuine projection: the label of a prime-strip. -/
def PrimeStrip.labelOf {Index Carrier : Type*} (s : PrimeStrip Index Carrier) : Index := s.label

/-- Genuine lemma: carrierOf is definitionally the carrier field. -/
theorem PrimeStrip.carrierOf_eq {Index Carrier : Type*} (s : PrimeStrip Index Carrier) :
    PrimeStrip.carrierOf s = s.carrier := rfl

end LeanFormal.IUT.XiFPaper.Mzk1PrimeStripObjectActualAdapted
