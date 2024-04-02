import Lake
open Lake DSL

package Jordan {
  -- add package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib Jordan {
  -- add library configuration options here
}
