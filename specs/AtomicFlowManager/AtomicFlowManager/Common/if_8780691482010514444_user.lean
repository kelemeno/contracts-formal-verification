import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.memory_array_index_access_struct_InteropCall_dyn
import generated.AtomicFlowManager.AtomicFlowManager.Common.if_1257063965892921583

import generated.AtomicFlowManager.AtomicFlowManager.Common.if_8780691482010514444_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

def A_if_8780691482010514444 (s₀ s₉ : State) : Prop := if_8780691482010514444_concrete_of_code.1 s₀ s₉

lemma if_8780691482010514444_abs_of_concrete {s₀ s₉ : State} :
  Spec if_8780691482010514444_concrete_of_code s₀ s₉ →
  Spec A_if_8780691482010514444 s₀ s₉ := by
  intro h
  simpa [A_if_8780691482010514444] using h

end

end AtomicFlowManager.Common
