import Clear.ReasoningPrinciple
import specs.KeccakDeterminism

/-
  THE KECCAK PRIMOP BRIDGE.

  `specs/KeccakDeterminism.lean` deliberately imports only `Clear.EVMState`: that
  minimal footprint is what keeps it buildable without the generated tree and lets
  it stay the axiom-free abstract layer.  It therefore cannot mention `primCall`.

  This module is the one-lemma bridge between the interpreter's primitive-call
  layer and `keccakOut`.  It is what makes Solidity mapping-slot derivation blocks
  tractable: `EVMKeccak256'` exposes a raw `Option` match that does not reduce
  until the branch is known, so proofs that consume a compiled block get stuck on
  an unreducible `multifill` argument.  Folding the match into `keccakOut` — whose
  definition already absorbs the collision fallback — removes the need to split the
  `Option` by hand.

  The same lemma was already present LOCALLY in
  `AtomicFlowManager/no_double_refund_user.lean` and used inline inside
  `InteropHandler/fun_verifyBundle_user.lean`'s `verify_slot_block`.  Hoisting it
  here so callers share one copy instead of rediscovering it — I lost two working
  sessions to keccak blocks before finding the second of those uses.
-/

namespace Clear.KeccakPrimOps

open Clear Clear.KeccakDeterminism EVMState Ast Expr Stmt FunctionDefinition
open State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps
open ReasoningPrinciple Utilities

/-- **The keccak PRIMOP in `keccakOut` form.**  Folds the raw `Option` match that
`EVMKeccak256'` produces into `keccakOut`. -/
lemma primCall_keccakOut {s : State} {a b : UInt256} :
    primCall s .Keccak256 [a, b]
      = (s.setEvm (keccakOut s.evm a b).2, [(keccakOut s.evm a b).1]) := by
  rw [EVMKeccak256']
  unfold keccakOut
  rcases hk : s.evm.keccak256 a b with _ | pr
  · simp only [hk]
  · simp only [hk]

/-! ## State-shape collapsing lemmas

Compiled-block hypotheses arrive as towers of `setEvm` applications with `.evm`
projections between them, which display as unreadable walls and block every
rewrite.  These two collapse the tower.  Together with `primCall_keccakOut` they
are what makes a mapping-slot block's hypothesis legible at all — before applying
them the goal is hundreds of characters of nested `🇪⟦…⟧`; after, it is a single
`match` over the keccak result.

NOTE the `Ok` restriction on `setEvm_Ok`.  The general form `(s🇪⟦e⟧).evm = e` is
FALSE: `setEvm` does not install the EVM on non-`Ok` states, so only the `Ok`-shaped
version holds. -/

/-- The EVM of an `Ok` state. -/
lemma evm_Ok (evm : EVM) (store : VarStore) : (Ok evm store).evm = evm := rfl

/-- `setEvm` on an `Ok` state yields an `Ok` state.  This is the rewrite that
collapses a chain of `setEvm`s, after which `evm_Ok` reduces the projections. -/
lemma setEvm_Ok (evm : EVM) (store : VarStore) (e : EVM) :
    (Ok evm store🇪⟦e⟧) = Ok e store := rfl

end Clear.KeccakPrimOps
