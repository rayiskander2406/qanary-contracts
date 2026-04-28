import Lake
open Lake DSL

package qanaryContracts where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "322515540d7f"

@[default_target]
lean_lib QanaryContracts
