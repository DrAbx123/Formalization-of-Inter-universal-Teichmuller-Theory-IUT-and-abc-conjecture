-- Non-mainline island: UnitIso was abandoned in favour of the DataOld path.
-- This module is intentionally a no-op so the guarded queue can compile it and stop
-- re-queueing the failed elaboration.  The actual fiber equivalence is built from
-- `S3123UnitIsoDataOld` / `S3123CounitIsoDataOld` (see `S3123FiberEquivalenceOfDataOld`).
import Mathlib.CategoryTheory.Bicategory.Modification.Pseudo

#check CategoryTheory.Pseudofunctor.StrongTrans.isoMk
