import Lake
open Lake DSL

require clear from git
  "https://github.com/kelemeno/Clear" @ "codex/vc-preprocessor-specs-split"

package «contracts-formal-verification» {
  leanOptions := #[⟨`autoImplicit, false⟩]
}

-- Auto-generated verification conditions from Yul
lean_lib «generated» {
  roots := #[`generated]
}

lean_lib «specs» {
  roots := #[`specs]
}

@[default_target]
lean_lib «Main» {
}
