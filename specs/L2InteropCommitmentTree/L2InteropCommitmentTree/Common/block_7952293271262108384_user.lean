import Clear.ReasoningPrinciple
import specs.StateOk

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.finalize_allocation

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.block_7952293271262108384_gen


namespace L2InteropCommitmentTree.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2InteropCommitmentTree L2InteropCommitmentTree

/-- **Finish the hash buffer**: third field, length word, allocation, and read back.

```
    split_expr_3 := add(p, 96); mstore(split_expr_3, _3)
    mstore(p, 96)                     -- the ABI length word: 96 bytes of payload
    finalize_allocation(p, 128)       -- reserve 128 = 32 (length) + 96 (fields)
    split_expr_4 := mload(p)          -- reads back 96
```

The length written at `p` is `96` and the amount reserved is `128`, so the buffer is the
length word plus exactly the three fields.  `split_expr_4` is then read back from `p` --
the hash length is taken from memory rather than being a literal, which is why the keccak
window is `[p+32, p+32+mload(p))` and closes exactly over the three fields. -/
def A_block_7952293271262108384 (s₀ s₉ : State) : Prop :=
  let a := s₀⟦"split_expr_3" ↦ s₀["expr_1562_mpos"]!! + 96⟧
  let m1 := a🇪⟦Clear.EVMState.mstore s₀.evm (a["split_expr_3"]!!) (a["_3"]!!)⟧
  let m2 := m1🇪⟦Clear.EVMState.mstore m1.evm (m1["expr_1562_mpos"]!!) 96⟧
  ∃ s, Spec (A_finalize_allocation (m2["expr_1562_mpos"]!!) 128) m2 s ∧
    s₉ = s⟦"split_expr_4" ↦ Clear.EVMState.mload s.evm (s["expr_1562_mpos"]!!)⟧

lemma block_7952293271262108384_abs_of_concrete {s₀ s₉ : State} :
  Spec block_7952293271262108384_concrete_of_code s₀ s₉ →
  Spec A_block_7952293271262108384 s₀ s₉ := by
  unfold block_7952293271262108384_concrete_of_code A_block_7952293271262108384
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s, hs, heq⟩ := hc
  exact ⟨s, hs, heq.symm⟩

end

end L2InteropCommitmentTree.Common
