import Lake
open Lake DSL

-- Pinned to commit 8ab513e (= upstream 0c672f4 + the `reverted` flag on EVMState,
-- branch `contracts-fv-reverted-flag`). This is the exact framework commit the proofs
-- are verified against; the reverted flag is required by the clean guard theorems
-- (#17/#18/#19). See framework_patches/README.md.
require clear from git
  "https://github.com/kelemeno/Clear" @ "8ab513e354954d459dd2b9862dae08d9721c5bfc"

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
