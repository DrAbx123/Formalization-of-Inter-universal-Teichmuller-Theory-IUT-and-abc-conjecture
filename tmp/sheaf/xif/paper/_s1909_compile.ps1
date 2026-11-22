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
$src = 'tmp/sheaf/xif/paper/S1909NormalRPrimeActual.lean'
$out = '.lake/build/lib/lean/tmp/sheaf/xif/paper/S1909NormalRPrimeActual.olean'
$stdout = 'D:\lean\s1909_stdout.txt'
$stderr = 'D:\lean\s1909_stderr.txt'
$success = $false
for ($i = 1; $i -le 30; $i++) {
  if (Test-Path $stdout) { Remove-Item $stdout -Force }
  if (Test-Path $stderr) { Remove-Item $stderr -Force }
  $p = Start-Process -FilePath $lean -ArgumentList @('-j1','-o',$out,$src) -NoNewWindow -PassThru -RedirectStandardOutput $stdout -RedirectStandardError $stderr
  $finished = $p.WaitForExit(900000)
  if (-not $finished) {
    try { $p.Kill() } catch {}
    Write-Output ("ATTEMPT " + $i + " TIMEOUT")
    Start-Sleep -Seconds 5
    continue
  }
  $code = $p.ExitCode
  Write-Output ("ATTEMPT " + $i + " EXIT " + $code)
  if ($code -eq 0) { $success = $true; break }
  Get-Content $stdout -Tail 3 -ErrorAction SilentlyContinue
  Get-Content $stderr -Tail 3 -ErrorAction SilentlyContinue
  Start-Sleep -Seconds 5
}
if ($success) { Write-Output 'SUCCESS' } else { Write-Output 'FAILED' }
