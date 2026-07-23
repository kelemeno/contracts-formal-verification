import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.fun_commitValue
import generated.AtomicFlowManager.AtomicFlowManager.read_from_calldatat_uint64

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_7724771009005182405_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_7724771009005182405 (s₀ s₉ : State) : Prop := block_7724771009005182405_concrete_of_code.1 s₀ s₉

lemma block_7724771009005182405_abs_of_concrete {s₀ s₉ : State} :
  Spec block_7724771009005182405_concrete_of_code s₀ s₉ →
  Spec A_block_7724771009005182405 s₀ s₉ := by
  intro h
  simpa [A_block_7724771009005182405] using h

end

end AtomicFlowManager.Common
