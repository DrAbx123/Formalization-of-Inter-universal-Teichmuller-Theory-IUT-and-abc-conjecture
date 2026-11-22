import tmp.sheaf.xif.paper.S2126Mod29IntegrationActual

/-!
# S2094 Mod-29 irreducibility target (accepted, complete)

This module is the stable consumer-facing path for

`s2094_f_irreducible : Irreducible f`

over `ZMod 29`. The proof together with all splitting lemmas lives in
`tmp.sheaf.xif.paper.S2126Mod29IntegrationActual`; its mathematical content is
the kernel-closed development of `S2122Mod29SplitActual`, copied verbatim.
This module re-exports it, so the declaration names and the target type are
unchanged and the previous placeholder proof is gone.

The re-export is complete; no added axioms are used.
-/
