$env:LEAN_PATH = ((@(
'D:\lean\.lake\packages\mathlib\.lake\build\lib\lean',
'D:\lean\.lake\packages\aesop\.lake\build\lib\lean',
'D:\lean\.lake\packages\batteries\.lake\build\lib\lean',
'D:\lean\.lake\packages\importGraph\.lake\build\lib\lean',
'D:\lean\.lake\packages\LeanSearchClient\.lake\build\lib\lean',
'D:\lean\.lake\packages\plausible\.lake\build\lib\lean',
'D:\lean\.lake\packages\proofwidgets\.lake\build\lib\lean',
'D:\lean\.lake\packages\Qq\.lake\build\lib\lean',
'D:\lean\.lake\build\lib\lean',
'C:\Users\Administrator\.elan\toolchains\leanprover--lean4---v4.32.2\lib\lean'
)) -join ';')
$env:LEAN_SRC_PATH = 'D:\lean'
$env:TMPDIR='D:\lean\.tmpbuild'
$lean = 'C:\Users\Administrator\.elan\toolchains\leanprover--lean4---v4.32.2\bin\lean.exe'
& $lean -j1 '-DrelaxedAutoImplicit=false' '-DmaxSynthPendingDepth=3' '-Dweak.linter.mathlibStandardSet=true' '-Dpp.unicode.fun=true' -o D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S2034OperationKummerActual.olean tmp/sheaf/xif/paper/S2034OperationKummerActual.lean
Write-Output ("EXIT=" + $LASTEXITCODE)