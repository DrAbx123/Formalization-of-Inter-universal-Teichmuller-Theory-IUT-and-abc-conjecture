/- v4.35 -> v4.32 shim (mainline, A864)
Upstream Mathlib (FLT271 pin) has `Mathlib.Topology.Algebra.Module.Equiv.Basic`;
our pinned Mathlib (905b95818e, lean v4.32.2) keeps the same material in
`Mathlib.Topology.Algebra.Module.Equiv`. This file only re-exports it so ported
FLT271 sources compile unchanged. -/
import Mathlib.Topology.Algebra.Module.Equiv