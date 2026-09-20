import Lake

/-!
# lakefile.lean
Created: 2026-09-10
Author: Koorosh Nobakhtfar
Pins Mathlib and registers oracle modules for explicit individual builds.
The library build selects Support only; cases are built by their module paths.
-/

open Lake DSL

package epistemic_oracles where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.34.0"

lean_lib Oracles where
  roots := #[`oracles]
  globs := #[.one `oracles]
