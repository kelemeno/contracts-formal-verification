import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.increment_uint256

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_2042036027024291676_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_2042036027024291676 (s₀ s₉ : State) : Prop := block_2042036027024291676_concrete_of_code.1 s₀ s₉

lemma block_2042036027024291676_abs_of_concrete {s₀ s₉ : State} :
  Spec block_2042036027024291676_concrete_of_code s₀ s₉ →
  Spec A_block_2042036027024291676 s₀ s₉ := by
  intro h
  simpa [A_block_2042036027024291676] using h

end

end AtomicFlowManager.Common
