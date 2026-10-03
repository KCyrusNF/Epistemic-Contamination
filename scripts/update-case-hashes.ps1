#requires -Version 5.1
<#
.SYNOPSIS
Update SHA-512 hashes for files listed in the case-path manifest.

.DESCRIPTION
File: scripts/update-case-hashes.ps1
Created: 03/10/2026
Author: Koorosh Nobakhtfar

Place this script in scripts/ at the repository root. Paths stored in the
manifest are relative to that root, independently of the working directory.

Hashes definition, lean_source, axiom_audit, and every listed results file
sequentially. Empty results arrays are skipped. Existing hashes are replaced
with lowercase SHA-512 hexadecimal strings. Each case requires a results array.

Hashes the exact file bytes: whitespace, encoding, and line endings matter.
Do not edit the listed files or manifest while this script runs.

Source files are never modified. The manifest is replaced only after every
entry succeeds, using a temporary file in the same directory. Output uses
UTF-8 without a BOM and CRLF line endings; JSON uses two-space indentation.

Exit codes: 0 = updated successfully; 1 = failed (manifest not replaced).

.PARAMETER Manifest
Manifest path. Relative paths are resolved from the repository root.
Defaults to manifests/case_paths.json.

.EXAMPLE
.\scripts\update-case-hashes.ps1

.EXAMPLE
.\scripts\update-case-hashes.ps1 -Manifest manifests/case_paths.json
#>

[CmdletBinding()]
param(
    [ValidateNotNullOrEmpty()]
    [string]$Manifest = 'manifests/case_paths.json'
)

Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'
$tempPath = $null

function Format-ManifestJson {
    param([string]$Json)

    # Format compact JSON without changing characters inside string values.
    $result = [System.Text.StringBuilder]::new()
    $depth = 0
    $inString = $false
    $escaped = $false

    foreach ($character in $Json.ToCharArray()) {
        if ($inString) {
            [void]$result.Append($character)

            if ($escaped) {
                $escaped = $false
            }
            elseif ($character -eq '\') {
                $escaped = $true
            }
            elseif ($character -eq '"') {
                $inString = $false
            }

            continue
        }

        switch ($character) {
            '"' {
                $inString = $true
                [void]$result.Append($character)
            }

            { $_ -eq '{' -or $_ -eq '[' } {
                $depth++
                [void]$result.Append($character)
                [void]$result.Append("`r`n" + ('  ' * $depth))
            }

            { $_ -eq '}' -or $_ -eq ']' } {
                $depth--
                [void]$result.Append("`r`n" + ('  ' * $depth))
                [void]$result.Append($character)
            }

            ',' {
                [void]$result.Append(",`r`n" + ('  ' * $depth))
            }

            ':' {
                [void]$result.Append(': ')
            }

            default {
                if (-not [char]::IsWhiteSpace($character)) {
                    [void]$result.Append($character)
                }
            }
        }
    }

    return $result.ToString() + "`r`n"
}

try {
    $repositoryRoot = [System.IO.Path]::GetFullPath(
        (Split-Path -Parent $PSScriptRoot)
    )

    if ([System.IO.Path]::IsPathRooted($Manifest)) {
        $manifestPath = [System.IO.Path]::GetFullPath($Manifest)
    }
    else {
        $manifestPath = [System.IO.Path]::GetFullPath(
            (Join-Path $repositoryRoot $Manifest)
        )
    }

    if (-not (Test-Path -LiteralPath $manifestPath -PathType Leaf)) {
        throw "Manifest not found: $manifestPath"
    }

    $initialHash = (
        Get-FileHash -LiteralPath $manifestPath -Algorithm SHA512
    ).Hash

    $data = Get-Content -LiteralPath $manifestPath -Raw -Encoding UTF8 |
        ConvertFrom-Json

    if ($null -eq $data -or $null -eq $data.PSObject.Properties['cases']) {
        throw 'Manifest must contain a cases array.'
    }

    if ($data.cases -isnot [array] -or $data.cases.Count -eq 0) {
        throw 'Manifest cases must be a nonempty array.'
    }

    $fields = @('definition', 'lean_source', 'axiom_audit')
    $filesToHash = [System.Collections.Generic.List[object]]::new()

    # Collect references to the original objects so hash updates reach $data.
    foreach ($case in $data.cases) {
        if ($null -eq $case -or $null -eq $case.PSObject.Properties['case_id']) {
            throw 'Each case must contain case_id.'
        }

        foreach ($field in $fields) {
            $property = $case.PSObject.Properties[$field]

            if ($null -eq $property -or $null -eq $property.Value) {
                throw "$($case.case_id): missing $field object."
            }

            $filesToHash.Add([pscustomobject]@{
                Location = "$($case.case_id).$field"
                Entry = $property.Value
            })
        }

        $resultsProperty = $case.PSObject.Properties['results']

        if ($null -eq $resultsProperty -or $resultsProperty.Value -isnot [array]) {
            throw "$($case.case_id): results must be an array (use [] when empty)."
        }

        for ($index = 0; $index -lt $case.results.Count; $index++) {
            $filesToHash.Add([pscustomobject]@{
                Location = "$($case.case_id).results[$index]"
                Entry = $case.results[$index]
            })
        }
    }

    $total = $filesToHash.Count
    $completed = 0

    # Apply the same validation and hashing rules to every file entry.
    foreach ($item in $filesToHash) {
        $entry = $item.Entry
        $location = $item.Location

        if ($null -eq $entry -or $entry -isnot [System.Management.Automation.PSCustomObject]) {
            throw "${location}: expected an object with path and sha512 fields."
        }

        if ($null -eq $entry.PSObject.Properties['path'] -or
            $null -eq $entry.PSObject.Properties['sha512']) {
            throw "${location}: expected path and sha512 fields."
        }

        $relativePath = $entry.path

        if ($relativePath -isnot [string] -or
            [string]::IsNullOrWhiteSpace($relativePath)) {
            throw "${location}: path must be a nonempty string."
        }

        if ([System.IO.Path]::IsPathRooted($relativePath) -or
            $relativePath.Contains(':') -or
            $relativePath.Contains('\') -or
            ($relativePath.Split('/') -contains '..')) {
            throw "${location}: expected a repository-relative path with forward slashes: $relativePath"
        }

        $sourcePath = Join-Path $repositoryRoot $relativePath

        if (-not (Test-Path -LiteralPath $sourcePath -PathType Leaf)) {
            throw "${location}: file not found: $relativePath"
        }

        $entry.sha512 = (
            Get-FileHash -LiteralPath $sourcePath -Algorithm SHA512
        ).Hash.ToLowerInvariant()

        $completed++
        Write-Host (
            "[{0}/{1}] {2}" -f $completed, $total, $relativePath
        )
    }

    $json = Format-ManifestJson -Json (
        ConvertTo-Json -InputObject $data -Depth 100 -Compress
    )

    $tempPath = Join-Path (Split-Path -Parent $manifestPath) (
        [System.IO.Path]::GetRandomFileName()
    )

    $encoding = [System.Text.UTF8Encoding]::new($false)
    [System.IO.File]::WriteAllText($tempPath, $json, $encoding)

    # Avoid overwriting edits made to the manifest during hashing.
    if ((Get-FileHash -LiteralPath $manifestPath -Algorithm SHA512).Hash -ne $initialHash) {
        throw 'Manifest changed during hashing. Run again after edits are complete.'
    }

    [System.IO.File]::Replace(
        $tempPath, $manifestPath,
        [System.Management.Automation.Language.NullString]::Value
    )
    $tempPath = $null

    Write-Host (
        "Updated {0} SHA-512 hashes in {1}" -f $completed, $manifestPath
    )
    exit 0
}
catch {
    [Console]::Error.WriteLine(
        "Hash update failed: {0}",
        $_.Exception.Message
    )
    exit 1
}
finally {
    if ($null -ne $tempPath -and (Test-Path -LiteralPath $tempPath)) {
        Remove-Item -LiteralPath $tempPath -Force -ErrorAction SilentlyContinue
    }
}
