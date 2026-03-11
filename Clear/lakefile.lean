import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"v4.27.0"

package «clear» {
  leanOptions := #[⟨`autoImplicit, false⟩]
}

@[default_target]
lean_lib «Clear» {}
