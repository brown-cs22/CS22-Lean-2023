import Lake
open Lake DSL


require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "e7e49c8a41239716cb79fa187a6bf66e7d82d710"
require autograder from git "https://github.com/robertylewis/cs22-lean-autograder" @ "1c6119111649e9c18594be3b3722836025a96e86"

package «brown-cs22» {
  -- add package configuration options here
}

lean_lib BrownCs22 {
  -- add library configuration options here
}

@[default_target]
lean_exe «brown-cs22» {
  root := `Main
}
