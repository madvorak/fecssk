import Lake
open Lake DSL

package fecssk {
  moreServerArgs := #["-DautoImplicit=false"]
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib Fecssk {
  globs := #[.submodules `Feccsk] 
  moreLeanArgs := #["-DautoImplicit=false"]
}
