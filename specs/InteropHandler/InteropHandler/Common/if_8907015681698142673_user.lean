import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.Common.block_3609567697964190809
import generated.InteropHandler.InteropHandler.abi_encode_bytes32_bytes_bytes
import generated.InteropHandler.InteropHandler.Common.block_3130800871317593083

import generated.InteropHandler.InteropHandler.Common.if_8907015681698142673_gen


/-
  REVERT-GATE of InteropHandler._requireExecutionAllowed:

      if iszero(expr) {
        { let memPtr := mload(64)
          let split_expr_12 := shl(226, 974221203)     -- error selector
          mstore(memPtr, split_expr_12)
          let split_expr_13 := add(memPtr, 4)
          let split_expr_14 := abi_encode_bytes32_bytes_bytes(
              split_expr_13, var_bundleHash, expr_mpos, _3) }
        { let split_expr_15 := sub(split_expr_14, memPtr)
          revert(memPtr, split_expr_15) }
      }

  `expr` is the authorization flag computed by the preceding block (1 iff the
  caller is the handler itself or the bundle's designated executor — see
  exec_allowed_user.lean).  If authorization SUCCEEDED (`expr ≠ 0`) this gate
  is a NO-OP: the state passes through verbatim.  If it FAILED (`expr = 0`)
  the body runs: it abi-encodes the error payload
  (bundleHash, formatEvmV1(chainid, caller), executionAddress) and reverts.

  HONESTY NOTES.
  * The body's two inner blocks are ABSTRACTED sub-blocks
    (block_3609567697964190809 = selector+abi_encode,
    block_3130800871317593083 = the revert(...) itself) whose abstract specs
    `A_block_*` live in their own files (currently stubs).  The failing
    branch is therefore characterized as the in-order routing through those
    two named sub-specs — this file cannot say more without editing them.
  * A `revert` in this model does NOT roll anything back and does NOT leave
    the Ok family: `revert(a,b)` = `evm_revert` = `evm_return`, which merely
    copies memory [a, a+b) into `return_data`.  So no `isOk`-based
    success/failure phrasing is possible; the gate's verification content is
    the PASS direction (authorized ⇒ state untouched, no revert data written)
    plus the routing of the failure direction.
-/

namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.InteropHandler InteropHandler

/-- **The revert-gate, genuinely**: if the authorization flag `expr` is set
(nonzero — caller authorized), the block is the IDENTITY on the state; if it
is zero (authorization failed), the final state is the in-order run of the
two named revert-payload sub-blocks (selector + abi-encode, then the revert
itself) from the untouched entry state. -/
def A_if_8907015681698142673 (s₀ s₉ : State) : Prop :=
  (s₀["expr"]!! ≠ 0 → s₉ = s₀)
  ∧ (s₀["expr"]!! = 0 →
      ∃ s₁ s₂, Spec A_block_3609567697964190809 s₀ s₁
             ∧ Spec A_block_3130800871317593083 s₁ s₂
             ∧ s₉ = s₂)

lemma if_8907015681698142673_abs_of_concrete {s₀ s₉ : State} :
  Spec if_8907015681698142673_concrete_of_code s₀ s₉ →
  Spec A_if_8907015681698142673 s₀ s₉ := by
  unfold if_8907015681698142673_concrete_of_code A_if_8907015681698142673
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hconcrete
  dsimp only at hconcrete
  obtain ⟨s₁, h1, s₂, h2, hfin⟩ := hconcrete
  by_cases h : (Ok evm store)["expr"]!! = 0
  · refine ⟨fun hne => absurd h hne, fun _ => ⟨s₁, s₂, h1, h2, ?_⟩⟩
    rw [if_pos h] at hfin
    exact hfin.symm
  · refine ⟨fun _ => ?_, fun h0 => absurd h0 h⟩
    rw [if_neg h] at hfin
    exact hfin.symm

end

end InteropHandler.Common
