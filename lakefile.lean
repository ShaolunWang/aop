import Lake
open Lake DSL

package «aop» where
  -- add package configuration options here

lean_lib «Aop» where
  -- add library configuration options here

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "9c2f17f68a9bd84e93f2a7a0fc8b8921c88c033e"

@[default_target]
lean_exe «aop» where
  root := `Main
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true
