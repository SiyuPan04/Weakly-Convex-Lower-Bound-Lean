$ErrorActionPreference = 'Stop'

$projectDir = $PSScriptRoot
$lakeCommand = Get-Command lake -ErrorAction SilentlyContinue
if ($null -eq $lakeCommand) {
  throw 'Lake was not found. Install Lean through elan, then rerun this script.'
}
$lakeExe = $lakeCommand.Source

$leanFiles = @(
  Get-Item -LiteralPath (Join-Path $projectDir 'WeaklyConvexLowerBound.lean')
) + @(
  Get-ChildItem -LiteralPath (Join-Path $projectDir 'WeaklyConvexLowerBound') `
    -Filter '*.lean' -File -Recurse
)

$forbiddenProofs = $leanFiles | Select-String `
  -Pattern '\bsorry\b|\badmit\b|\bsorryAx\b|\bopaque\b|^\s*axiom\b'
if ($forbiddenProofs) {
  $forbiddenProofs | ForEach-Object { Write-Host $_ }
  throw 'Forbidden proof placeholder, opaque declaration, or project axiom found.'
}

$privatePathPatterns = @(
  '[A-Za-z]:[/\\](?:Use' + 'rs|Documents and Settings)[/\\]',
  '/Use' + 'rs/[^/]+/',
  '/ho' + 'me/[^/]+/'
)
$leakPattern = '(?i)(' + ($privatePathPatterns -join '|') + ')'
$publicFiles = Get-ChildItem -LiteralPath $projectDir -File -Recurse |
  Where-Object { $_.FullName -notmatch '[\\/]\.lake[\\/]' -and $_.FullName -notmatch '[\\/]\.git[\\/]' }
$leaks = $publicFiles | Select-String -Pattern $leakPattern
if ($leaks) {
  $leaks | ForEach-Object { Write-Host $_ }
  throw 'Private absolute path found.'
}

$foreignImports = $leanFiles | Select-String `
  -Pattern '^import\s+(?!Mathlib(?:\.|$)|WeaklyConvexLowerBound(?:\.|$))'
if ($foreignImports) {
  $foreignImports | ForEach-Object { Write-Host $_ }
  throw 'A Lean module imports a package other than mathlib or this project.'
}

$expectedRootImports = Get-ChildItem `
    -LiteralPath (Join-Path $projectDir 'WeaklyConvexLowerBound') `
    -Filter '*.lean' -File -Recurse |
  Where-Object {
    $_.Name -ne 'AxiomAudit.lean' -and
    $_.FullName -notmatch '[\\/]Foundation[\\/]'
  } |
  ForEach-Object {
    $relativePath = $_.FullName.Substring($projectDir.Length + 1)
    $relativePath.Substring(0, $relativePath.Length - 5) -replace '[\\/]', '.'
  } |
  Sort-Object
$actualRootImports = Get-Content `
    -LiteralPath (Join-Path $projectDir 'WeaklyConvexLowerBound.lean') |
  Where-Object { $_ -match '^import\s+' } |
  ForEach-Object { ($_ -replace '^import\s+', '').Trim() } |
  Sort-Object
$rootImportDifference = Compare-Object $expectedRootImports $actualRootImports
if ($rootImportDifference) {
  $rootImportDifference | ForEach-Object { Write-Host $_ }
  throw 'The root module does not import every non-audit proof module exactly once.'
}

Push-Location $projectDir
try {
  & $lakeExe build
  if ($LASTEXITCODE -ne 0) { throw "lake build failed with exit code $LASTEXITCODE" }

  & $lakeExe env lean 'WeaklyConvexLowerBound/AxiomAudit.lean'
  if ($LASTEXITCODE -ne 0) { throw "axiom audit failed with exit code $LASTEXITCODE" }
} finally {
  Pop-Location
}

Write-Host 'Verification passed: standalone build, root coverage, axiom audit, placeholder scan, and leak scan succeeded.'
