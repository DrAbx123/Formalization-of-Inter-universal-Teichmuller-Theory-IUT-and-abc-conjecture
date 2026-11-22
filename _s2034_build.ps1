
$ErrorActionPreference = 'Continue'
$paths = @(
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
)
$env:LEAN_PATH = ($paths -join ';')
$env:LEAN_SRC_PATH = 'D:\lean'
$lean = 'C:\Users\Administrator\.elan\toolchains\leanprover--lean4---v4.32.2\bin\lean.exe'
$env:TMPDIR='D:\lean\.tmpbuild'
New-Item -ItemType Directory -Force -Path $env:TMPDIR | Out-Null
$src = $args[0]
$out = 'D:\lean\.lake\build\lib\lean\' + ($src -replace '\.lean$','.olean')
$sw = [System.Diagnostics.Stopwatch]::StartNew()
& $lean -j1 -o $out $src
Write-Output ("EXIT=" + $LASTEXITCODE + " ELAPSED=" + $sw.Elapsed.TotalSeconds)
