import Lake
open Lake DSL

package erdos_ternary where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.14.0"

@[default_target]
lean_lib Erdos where

lean_lib ErdosCompute where

lean_lib ErdosFinal where

lean_lib ErdosAnalytical where
