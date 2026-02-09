import Lake
open Lake DSL

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.27.0"

package «combinatorial_designs» where
  -- add package configuration options here

@[default_target]
lean_lib CombinatorialDesign
