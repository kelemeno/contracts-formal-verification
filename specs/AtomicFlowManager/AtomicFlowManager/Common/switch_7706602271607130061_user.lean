import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.memory_array_index_access_struct_InteropCall_dyn
import generated.AtomicFlowManager.AtomicFlowManager.fun_efficientHash

import generated.AtomicFlowManager.AtomicFlowManager.Common.switch_7706602271607130061_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_switch_7706602271607130061 (s₀ s₉ : State) : Prop := switch_7706602271607130061_concrete_of_code.1 s₀ s₉

lemma switch_7706602271607130061_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_7706602271607130061_concrete_of_code s₀ s₉ →
  Spec A_switch_7706602271607130061 s₀ s₉ := by
  intro h
  simpa [A_switch_7706602271607130061] using h

end

end AtomicFlowManager.Common
