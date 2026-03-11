import Lake
open Lake DSL

require clear from "Clear"

package «contracts-formal-verification» {
  leanOptions := #[⟨`autoImplicit, false⟩]
}

lean_lib «generated» {
  globs := #[
    .andSubmodules `generated.DiamondProxy,
    .andSubmodules `generated.L1AssetRouter,
    .andSubmodules `generated.L1Nullifier
  ]
}

@[default_target]
lean_lib «specs» {
  globs := #[
    .andSubmodules `specs.DiamondProxy,
    .andSubmodules `specs.L1AssetRouter,
    .andSubmodules `specs.L1Nullifier
  ]
}
