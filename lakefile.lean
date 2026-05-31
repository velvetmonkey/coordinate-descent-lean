import Lake
open Lake DSL

require "leanprover-community" / "mathlib" @ git "v4.28.0"

package «CoordinateDescent» where

@[default_target]
lean_lib «CoordinateDescent» where
