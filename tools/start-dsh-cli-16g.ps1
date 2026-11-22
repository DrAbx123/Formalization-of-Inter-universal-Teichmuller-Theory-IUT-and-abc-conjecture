param(
  [int]$Port = 8080,
  [string]$Profile = 'fullweb',
  [switch]$Open
)
$ErrorActionPreference = 'Stop'
$wrapper = 'D:\lean\tools\dsh-16g\dsh-16g.ps1'
if (-not (Test-Path -LiteralPath $wrapper)) { throw "Missing wrapper: $wrapper" }
$appArgs = @($Profile, '--no-open', '--port', "$Port")
if ($Open) { $appArgs = @($Profile, '--port', "$Port") }
Write-Host "Starting DSH CLI profile '$Profile' on port $Port with 16GB node heap..."
& $wrapper @appArgs
exit $LASTEXITCODE
