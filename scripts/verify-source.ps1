param(
    [string]$PythonExecutable = 'python',
    [string]$LakeExecutable = 'lake'
)

$ErrorActionPreference = 'Stop'
$repoRoot = Split-Path -Parent $PSScriptRoot

Push-Location (Join-Path $repoRoot 'r55')
try {
    & $PythonExecutable -m unittest `
        test_catalog_certificate test_ramsey test_pilot_runner
    if ($LASTEXITCODE -ne 0) {
        throw 'Python tests failed.'
    }
    & $PythonExecutable catalog_certificate.py verify `
        . r35_extension_certificate.json
    if ($LASTEXITCODE -ne 0) {
        throw 'Catalogue certificate verification failed.'
    }
} finally {
    Pop-Location
}

Push-Location $repoRoot
try {
    & $PythonExecutable scripts\r45_d8_pilot\gen358_lean_certificate.py verify
    if ($LASTEXITCODE -ne 0) {
        throw 'gen358 Lean certificate verification failed.'
    }
} finally {
    Pop-Location
}

Push-Location (Join-Path $repoRoot 'vendor\lrat-catcher')
try {
    & $LakeExecutable build `
        LRATCatcher.Tests.R35CatalogCheckpoint `
        LRATCatcher.Tests.R55W5Symmetry `
        LRATCatcher.Tests.R55CommonNeighborhoodBridge `
        LRATCatcher.Tests.R55CanonicalUnitsBridge `
        LRATCatcher.Tests.R55TypedUnitsBridge `
        LRATCatcher.Tests.R55CanonicalCommonIndex `
        LRATCatcher.Tests.R55ColoringPermutation `
        LRATCatcher.Tests.R55CanonicalRelabeling `
        LRATCatcher.Tests.RamseyUpperBounds `
        LRATCatcher.Tests.R55DegreeBounds `
        LRATCatcher.Tests.R45DegreeEightCover `
        LRATCatcher.Tests.R45DegreeEightPilot
    if ($LASTEXITCODE -ne 0) {
        throw 'Lean integration build failed.'
    }
} finally {
    Pop-Location
}

Write-Host 'Source verification completed successfully.' -ForegroundColor Green
