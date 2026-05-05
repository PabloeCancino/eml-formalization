import Lake
open Lake DSL

package EML where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.29.1"

lean_lib EML where
  roots := #[`EML.EML]
