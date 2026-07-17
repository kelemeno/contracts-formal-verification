import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.abi_encode_bool_uint256_uint64

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_2416147463009286373_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_if_2416147463009286373 (s₀ s₉ : State) : Prop := sorry

lemma if_2416147463009286373_abs_of_concrete {s₀ s₉ : State} :
  Spec if_2416147463009286373_concrete_of_code s₀ s₉ →
  Spec A_if_2416147463009286373 s₀ s₉ := by
  sorry

end

end AtomicFlowManager.Common
