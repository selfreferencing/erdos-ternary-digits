import Lake
open Lake DSL

package erdos_ternary where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.14.0"

lean_lib ErdosTernaryBase where

lean_lib ErdosTernaryOrbit where

lean_lib ErdosFourier where

lean_lib ErdosTermination where

@[default_target]
lean_lib ErdosTernaryDigits where
