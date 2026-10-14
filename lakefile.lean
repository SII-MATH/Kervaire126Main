import Lake
open Lake DSL

package Kervaire126Main where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "905b95818eb32af7874a58b427f50c1711a5e96c"

@[default_target]
lean_lib KIP126 where
  globs := #[.one `KIP126, .submodules `KIP126.Def.SpectralSequence]
