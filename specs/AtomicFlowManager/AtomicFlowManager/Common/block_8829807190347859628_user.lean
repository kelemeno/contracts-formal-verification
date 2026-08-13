import Clear.ReasoningPrinciple
import specs.StateOk


import generated.AtomicFlowManager.AtomicFlowManager.Common.block_8829807190347859628_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities 

/-- **Lay out the first two leaf fields in a fresh buffer.**

```
    expr_2619_mpos := mload(64)      -- the free pointer, p
    _4 := add(p, 32); mstore(_4, _1)
    split_expr_2 := add(p, 64); mstore(split_expr_2, _2)
```

The buffer starts at the CURRENT free pointer and the fields go at `p+32` and `p+64`,
leaving `p` itself for the length word written next. -/
def A_block_8829807190347859628 (s₀ s₉ : State) : Prop :=
  let a := s₀⟦"expr_2619_mpos" ↦ Clear.EVMState.mload s₀.evm 64⟧
  let b := a⟦"_4" ↦ a["expr_2619_mpos"]!! + 32⟧
  let m1 := b🇪⟦Clear.EVMState.mstore s₀.evm (b["_4"]!!) (b["_1"]!!)⟧
  let c := m1⟦"split_expr_2" ↦ m1["expr_2619_mpos"]!! + 64⟧
  s₉ = c🇪⟦Clear.EVMState.mstore m1.evm (c["split_expr_2"]!!) (c["_2"]!!)⟧

lemma block_8829807190347859628_abs_of_concrete {s₀ s₉ : State} :
  Spec block_8829807190347859628_concrete_of_code s₀ s₉ →
  Spec A_block_8829807190347859628 s₀ s₉ := by
  unfold block_8829807190347859628_concrete_of_code A_block_8829807190347859628
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  exact hc.symm

end

end AtomicFlowManager.Common
