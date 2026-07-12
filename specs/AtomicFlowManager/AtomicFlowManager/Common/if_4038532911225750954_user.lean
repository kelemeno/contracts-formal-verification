import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.abi_encode_uint256_uint256_7396

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_4038532911225750954_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_if_4038532911225750954 (s₀ s₉ : State) : Prop := if_4038532911225750954_concrete_of_code.1 s₀ s₉

lemma if_4038532911225750954_abs_of_concrete {s₀ s₉ : State} :
  Spec if_4038532911225750954_concrete_of_code s₀ s₉ →
  Spec A_if_4038532911225750954 s₀ s₉ := by
  intro h
  simpa [A_if_4038532911225750954] using h

end

end AtomicFlowManager.Common
