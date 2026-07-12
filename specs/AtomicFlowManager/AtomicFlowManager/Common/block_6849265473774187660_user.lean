import Clear.ReasoningPrinciple

import generated.AtomicFlowManager.AtomicFlowManager.validator_revert_bool

import generated.AtomicFlowManager.AtomicFlowManager.Common.block_6849265473774187660_gen


namespace AtomicFlowManager.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.AtomicFlowManager AtomicFlowManager

def A_block_6849265473774187660 (s₀ s₉ : State) : Prop := block_6849265473774187660_concrete_of_code.1 s₀ s₉

lemma block_6849265473774187660_abs_of_concrete {s₀ s₉ : State} :
  Spec block_6849265473774187660_concrete_of_code s₀ s₉ →
  Spec A_block_6849265473774187660 s₀ s₉ := by
  intro h
  simpa [A_block_6849265473774187660] using h

end

end AtomicFlowManager.Common
