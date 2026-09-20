import oracles.Support

/-!
# oracles.lean
Created: 20/09/2026
Author: Koorosh Nobakhtfar

Root module for the oracle library. Imports shared Support only.

Together with the root selection in lakefile.lean, this module makes
individual case modules available as explicit build targets while keeping
library builds limited to this module and Support's dependencies.

Case oracles are built individually. Do not add case imports here.
-/