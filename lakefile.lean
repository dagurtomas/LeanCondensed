import Lake
open Lake DSL

package «LeanCondensed» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`autoImplicit, false⟩, -- prevents typos to be interpreted as new free variables
    ⟨`relaxedAutoImplicit, false⟩, -- prevents typos to be interpreted as new free variables
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «LeanCondensed» where
  -- add any library configuration options here
