import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.abi_decode_struct_BundleAttributes

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_2975674517988169047_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_2975674517988169047 (s₀ s₉ : State) : Prop := block_2975674517988169047_concrete_of_code.1 s₀ s₉

lemma block_2975674517988169047_abs_of_concrete {s₀ s₉ : State} :
  Spec block_2975674517988169047_concrete_of_code s₀ s₉ →
  Spec A_block_2975674517988169047 s₀ s₉ := by
  intro h
  simpa [A_block_2975674517988169047] using h

end

end AtomicFlowManager.Common
