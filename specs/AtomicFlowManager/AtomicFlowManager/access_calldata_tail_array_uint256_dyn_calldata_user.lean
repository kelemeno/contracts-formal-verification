import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_6743186873342481897
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_5731116343986243113
import generated.AtomicFlowManager.AtomicFlowManager.Common.if_1209118431116190868
import generated.AtomicFlowManager.AtomicFlowManager.Common.if_6747681429752853338
import generated.AtomicFlowManager.AtomicFlowManager.Common.if_8835011984658778953

import generated.AtomicFlowManager.AtomicFlowManager.access_calldata_tail_array_uint256_dyn_calldata_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common 

/-- State after `addr_1 := add(base_ref, rel_offset_of_tail); length := calldataload(addr_1)`. -/
def tailLoadLenUint256 (s : State) : State :=
  s⟦"addr_1" ↦ s["base_ref"]!! + (s["rel_offset_of_tail"]!!)⟧⟦"length" ↦
    Clear.EVMState.calldataload s.evm
      ((s⟦"addr_1" ↦ s["base_ref"]!! + (s["rel_offset_of_tail"]!!)⟧)["addr_1"]!!)⟧

/-- State after `addr := add(addr_1, 32); split_expr_5 := calldatasize();
split_expr_6 := shl(5, length); split_expr_7 := sub(split_expr_5, split_expr_6)`.
`shl(5, length)` is `length * 32` — the array's byte span. -/
def tailBoundUint256 (s : State) : State :=
  let t := s⟦"addr" ↦ s["addr_1"]!! + 32⟧⟦"split_expr_5" ↦
    (s.evm.execution_env.input_data.size : UInt256)⟧
  let u := Clear.State.multifill ["split_expr_6"] [Fin.shiftLeft (t["length"]!!) 5] t
  u⟦"split_expr_7" ↦ u["split_expr_5"]!! - (u["split_expr_6"]!!)⟧

/-- **The dynamic-array calldata accessor**, in full.

```
    function access_calldata_tail_array_uint256_dyn_calldata(base_ref, ptr_to_tail)
        -> addr, length
```

Every check it performs is now a closed spec, and together they are solc's
complete calldata-decoding discipline for a dynamic tail:

1. `block_6743186873342481897` — the bound `calldatasize - base_ref - 31`.
2. `block_5731116343986243113` — the tail offset compared to it, SIGNED.
3. `if_1209118431116190868` — revert unless the tail leaves room for its length word.
4. `length := calldataload(base_ref + rel_offset)`, then
   `if_6747681429752853338` — reject a length above `2^64 - 1`.
5. `addr := addr_1 + 32`, and `if_8835011984658778953` — reject unless the array's
   byte span `length * 32` fits in the remaining calldata, again SIGNED.

So an `(addr, length)` pair returned by this function is backed by real calldata:
the elements lie inside the input, and the length cannot have been inflated to
make the caller read past the end.  That is the assumption every indexed access
above it relies on, including the ascending-order loops.

The out parameters are bound LAST (`length` then `addr`) after the store is
restored, which is why the final state reads them out of `s₅`. -/
def A_access_calldata_tail_array_uint256_dyn_calldata
    (addr length : Identifier) (base_ref ptr_to_tail : Literal) (s₀ s₉ : State) : Prop :=
  ∃ s₁, Spec AtomicFlowManager.Common.A_block_6743186873342481897
      (s₀☎️⟦["base_ref", "ptr_to_tail"],[base_ref, ptr_to_tail]⟧) s₁ ∧
    ∃ s₂, Spec AtomicFlowManager.Common.A_block_5731116343986243113 s₁ s₂ ∧
      ∃ s₃, Spec AtomicFlowManager.Common.A_if_1209118431116190868 s₂ s₃ ∧
        ∃ s₄, Spec AtomicFlowManager.Common.A_if_6747681429752853338 (tailLoadLenUint256 s₃) s₄ ∧
          ∃ s₅, Spec AtomicFlowManager.Common.A_if_8835011984658778953 (tailBoundUint256 s₄) s₅ ∧
            s₉ = 🧟s₅🏪⟦s₀⟧⟦length ↦ s₅["length"]!!⟧⟦addr ↦ s₅["addr"]!!⟧

lemma access_calldata_tail_array_uint256_dyn_calldata_abs_of_concrete {s₀ s₉ : State} {addr length base_ref ptr_to_tail} :
  Spec (access_calldata_tail_array_uint256_dyn_calldata_concrete_of_code.1 addr length base_ref ptr_to_tail) s₀ s₉ →
  Spec (A_access_calldata_tail_array_uint256_dyn_calldata addr length base_ref ptr_to_tail) s₀ s₉ := by
  unfold access_calldata_tail_array_uint256_dyn_calldata_concrete_of_code
    A_access_calldata_tail_array_uint256_dyn_calldata tailLoadLenUint256 tailBoundUint256
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, heq⟩ := hc
  exact ⟨s₁, h₁, s₂, h₂, s₃, h₃, s₄, h₄, s₅, h₅, heq.symm⟩

end

end generated.AtomicFlowManager.AtomicFlowManager
