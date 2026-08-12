import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.memory_array_index_access_struct_InteropCall_dyn
import generated.AtomicFlowManager.AtomicFlowManager.Common.if_1257063965892921583

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_8780691482010514444_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

/-- The LEFT-CHILD wrapper of the zero-cascade check:

    if iszero(split_expr_2) {            -- mask bit `var_i` is 0, i.e. a left child
        let split_expr_4 := memory_array_index_access_struct_InteropCall_dyn(..., var_i)
        let _3 := mload(split_expr_4)    -- the right sibling at this level
        if iszero(eq(_3, var_zeroSubtreeHash)) { revert(...) } }

Note how the generator compiles this: the accessor and the inner guard are evaluated
UNCONDITIONALLY, and only the final state selection consults the mask bit
(`if split_expr_2 = 0 then ss else s₀`). So the spec keeps that shape rather than pushing
the branch outward.

`LastBatchInRoot.RightEmpty` is this, one level: "at every level where the node is a left
child, the right sibling's subtree is empty". -/
def A_if_8780691482010514444 (s₀ s₉ : State) : Prop :=
  let p := s₀⟦"split_expr_3" ↦ EVMState.mload s₀.evm (s₀["_2"]!!)⟧
  ∃ s, Spec (A_memory_array_index_access_struct_InteropCall_dyn "split_expr_4"
              (p["split_expr_3"]!!) (p["var_i"]!!)) p s ∧
    (let q := s⟦"_3" ↦ EVMState.mload s.evm (s["split_expr_4"]!!)⟧
     let r := q⟦"split_expr_5" ↦ (decide (q["_3"]!! = q["var_zeroSubtreeHash"]!!)).toUInt256⟧
     ∃ ss, Spec A_if_1257063965892921583 r ss ∧
       (if s₀["split_expr_2"]!! = 0 then ss else s₀) = s₉)

lemma if_8780691482010514444_abs_of_concrete {s₀ s₉ : State} :
  Spec if_8780691482010514444_concrete_of_code s₀ s₉ →
  Spec A_if_8780691482010514444 s₀ s₉ := by
  unfold if_8780691482010514444_concrete_of_code A_if_8780691482010514444
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  exact hc
end

end AtomicFlowManager.Common
