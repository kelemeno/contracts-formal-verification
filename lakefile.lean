import Lake
open Lake DSL

require clear from "Clear"

package «contracts-formal-verification» {
  leanOptions := #[⟨`autoImplicit, false⟩]
}

@[default_target]
lean_lib «specs» {
  globs := #[
    .andSubmodules `specs.DiamondProxy,
    .andSubmodules `specs.L1AssetRouter,
    .andSubmodules `specs.L1Nullifier
  ]
}
