import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.abi_encode_uint256_uint64

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_6867747978864521234_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_if_6867747978864521234 (s₀ s₉ : State) : Prop := if_6867747978864521234_concrete_of_code.1 s₀ s₉

lemma if_6867747978864521234_abs_of_concrete {s₀ s₉ : State} :
  Spec if_6867747978864521234_concrete_of_code s₀ s₉ →
  Spec A_if_6867747978864521234 s₀ s₉ := by
  intro h
  simpa [A_if_6867747978864521234] using h

end

end AtomicFlowManager.Common
