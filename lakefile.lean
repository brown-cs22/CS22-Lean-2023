import Lake
open Lake DSL


require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "724a444a35a78ce1922f5c3626ff618f50976f62"
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
