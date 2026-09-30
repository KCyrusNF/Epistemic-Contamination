#requires -Version 5.1
<#
.SYNOPSIS
Validate every test case definition under the repository's test_cases directory.
.DESCRIPTION
File: scripts/validate-all-test-cases.ps1
Created: 30/09/2026
Author: Koorosh Nobakhtfar

Runs validate_case_definition.py sequentially for each JSON file, including
nested domain folders. That validator imports check_json_syntax.py, so syntax
and duplicate-key checks run before structural validation without double parsing.

Paths are resolved from this script's location, independently of the working
directory. Keep this script beside the two Python validators in scripts/.
No case files are modified. This does not build Lean or check mathematical meaning.

Exit codes: 0 = all passed; 1 = invalid cases; 2 = setup/read/execution error
(including an empty test_cases directory). Execution errors take precedence.
.PARAMETER Python
Python 3.9+ executable name or full path. Defaults to python.
.PARAMETER PythonArguments
Optional interpreter arguments, for example -3 when using the Windows py launcher.
.EXAMPLE
.\scripts\validate-all-test-cases.ps1
.EXAMPLE
.\scripts\validate-all-test-cases.ps1 -Python py -PythonArguments '-3'
#>
[CmdletBinding()]
param(
    [ValidateNotNullOrEmpty()]
    [string]$Python = 'python',
    [string[]]$PythonArguments = @()
)

Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'

# Handle native exit codes explicitly, including on PowerShell 7.3+.
$PSNativeCommandUseErrorActionPreference = $false

function Invoke-ValidatorPython {
    param([string[]]$Arguments)

    # Windows PowerShell may surface native stderr as nonterminating errors.
    # Preserve diagnostics and use the process exit code to classify the result.
    $ErrorActionPreference = 'Continue'

    # Native commands update the global exit code. Read that scope explicitly
    # so a caller's local LASTEXITCODE cannot hide the actual process result.
    $global:LASTEXITCODE = 2

    & $script:pythonExecutable @PythonArguments @Arguments | Out-Host
    $script:pythonExitCode = $global:LASTEXITCODE
}

try {
    $repositoryRoot = Split-Path -Parent $PSScriptRoot
    $casesDirectory = Join-Path $repositoryRoot 'test_cases'
    $validatorPath = Join-Path $PSScriptRoot 'validate_case_definition.py'
    $syntaxPath = Join-Path $PSScriptRoot 'check_json_syntax.py'

    foreach ($requiredFile in @($validatorPath, $syntaxPath)) {
        if (-not (Test-Path -LiteralPath $requiredFile -PathType Leaf)) {
            throw "Required validator not found: $requiredFile"
        }
    }

    if (-not (Test-Path -LiteralPath $casesDirectory -PathType Container)) {
        throw "Test case directory not found: $casesDirectory"
    }

    $pythonExecutable = (Get-Command -Name $Python -CommandType Application -ErrorAction Stop |
        Select-Object -First 1).Source

    $pythonExitCode = 2
    Invoke-ValidatorPython -Arguments @('-c', 'import sys; sys.exit(0 if sys.version_info >= (3, 9) else 2)')

    if ($pythonExitCode -ne 0) {
        throw 'Python 3.9 or newer is required and must start successfully.'
    }

    $files = @(Get-ChildItem -LiteralPath $casesDirectory -Recurse -File -Filter '*.json' |
        Sort-Object FullName)

    if ($files.Count -eq 0) {
        throw "No JSON test case files found in: $casesDirectory"
    }

    $passed = 0
    $invalid = 0
    $executionErrors = 0
    $failedFiles = [System.Collections.Generic.List[string]]::new()

    Write-Host ("Checking {0} test case definitions (syntax and structure)." -f $files.Count)

    for ($index = 0; $index -lt $files.Count; $index++) {
        $caseFile = $files[$index]
        $relativePath = $caseFile.FullName.Substring($casesDirectory.Length + 1)

        Write-Host ("`n[{0}/{1}] {2}" -f ($index + 1), $files.Count, $relativePath)

        $pythonExitCode = 2
        Invoke-ValidatorPython -Arguments @($validatorPath, $caseFile.FullName)

        if ($pythonExitCode -eq 0) {
            $passed++
        }
        elseif ($pythonExitCode -eq 1) {
            $invalid++
            $failedFiles.Add("INVALID: $relativePath")
        }
        else {
            $executionErrors++
            $failedFiles.Add("ERROR (exit $pythonExitCode): $relativePath")
        }
    }

    Write-Host ("`nSummary: {0} checked; {1} passed; {2} invalid; {3} execution/read errors." -f
        $files.Count, $passed, $invalid, $executionErrors)

    foreach ($failure in $failedFiles) {
        Write-Host $failure
    }

    if ($executionErrors -gt 0) { exit 2 }
    if ($invalid -gt 0) { exit 1 }

    exit 0
}
catch {
    [Console]::Error.WriteLine("Validation could not complete: {0}", $_.Exception.Message)
    exit 2
}
