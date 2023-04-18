import Lake
open Lake DSL

package «Entemology»

-- lean_lib Entemology

@[default_target]
lean_lib «Entemology» {
  roots := #[`Entemology]
}

-- NOTE: this must be 'm'mathlib, as indicated from:
--  https://github.com/leanprover-community/mathlib4#using-mathlib4-as-a-dependency
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "72b511e"

meta if get_config? env = some "dev" then -- dev is so not everyone has to build it
  require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "b9421b9"

