import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.checked_add_uint256

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_7729555111419488802_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_7729555111419488802 (s₀ s₉ : State) : Prop := block_7729555111419488802_concrete_of_code.1 s₀ s₉

lemma block_7729555111419488802_abs_of_concrete {s₀ s₉ : State} :
  Spec block_7729555111419488802_concrete_of_code s₀ s₉ →
  Spec A_block_7729555111419488802 s₀ s₉ := by
  intro h
  simpa [A_block_7729555111419488802] using h

end

end AtomicFlowManager.Common
