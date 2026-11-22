def main : IO Unit := do
  let b <- IO.FS.readFile "D:\lean\.lake\packages\mathlib\.lake\build\lib\lean\Mathlib\AlgebraicTopology\SimplicialSet\Homology\Nondegenerate.olean.private"
  IO.println s!"read {b.length}"
#eval main
