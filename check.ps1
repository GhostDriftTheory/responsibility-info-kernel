$ErrorActionPreference = "Stop"

Write-Host "== Responsibility Info Kernel CI check =="

$requiredFiles = @(
  "lean-toolchain",
  "lakefile.lean",
  "lake-manifest.json",
  "ResponsibilityInfoKernel.lean",
  "GenericNoncommutativity.lean"
)

foreach ($file in $requiredFiles) {
  if (-not (Test-Path -LiteralPath $file)) {
    throw "Required file is missing: $file"
  }
}

Write-Host "Lean toolchain:"
Get-Content -LiteralPath "lean-toolchain"

Write-Host "Lake version:"
lake --version

Write-Host "Fetching cached dependency oleans when available..."
lake exe cache get

Write-Host "Building ResponsibilityOS dependency..."
lake build ResponsibilityOS

Write-Host "Checking ResponsibilityInfoKernel.lean..."
lake env lean ResponsibilityInfoKernel.lean

Write-Host "Checking GenericNoncommutativity.lean..."
lake env lean GenericNoncommutativity.lean

Write-Host "All Lean checks passed."
