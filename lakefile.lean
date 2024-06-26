import Lake
open Lake DSL

package «controlbits» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Controlbits» {
  -- add any library configuration options here
}

meta if get_config? env = some "dev" then -- dev is so not everyone has to build it
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"
require Paperproof from git "https://github.com/Paper-Proof/paperproof.git"@"main"/"lean"
