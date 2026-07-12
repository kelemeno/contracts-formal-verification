import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_1050661087314198911
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_3281893837970501813
import generated.AtomicFlowManager.AtomicFlowManager.finalize_allocation
import generated.AtomicFlowManager.AtomicFlowManager.Common.block_7062530953133995134

import generated.AtomicFlowManager.AtomicFlowManager.fun_commitValue_gen


namespace generated.AtomicFlowManager.AtomicFlowManager

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities AtomicFlowManager.Common generated.AtomicFlowManager AtomicFlowManager

def A_fun_commitValue (var : Identifier) (var_flowId var_specHash : Literal) (s₀ s₉ : State) : Prop := fun_commitValue_concrete_of_code.1 var var_flowId var_specHash s₀ s₉

lemma fun_commitValue_abs_of_concrete {s₀ s₉ : State} {var var_flowId var_specHash} :
  Spec (fun_commitValue_concrete_of_code.1 var var_flowId var_specHash) s₀ s₉ →
  Spec (A_fun_commitValue var var_flowId var_specHash) s₀ s₉ := by
  intro h
  simpa [A_fun_commitValue] using h

end

end generated.AtomicFlowManager.AtomicFlowManager
