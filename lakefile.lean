import Lake
open Lake DSL

package «zerosum» {
  -- add package configuration options here
}

lean_lib «Zerosum» {

  -- add library configuration options here
}

@[default_target]
lean_exe «zerosum» {
  root := `Main
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"