import Lake
open Lake DSL

package «GameTheory» {
  -- add package configuration options here
}

lean_lib «GameTheory» {

  -- add library configuration options here
}

@[default_target]
lean_exe «Game» {
  root := `Main
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
