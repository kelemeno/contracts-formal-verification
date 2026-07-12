import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.abi_encode_struct_L2Message

import generated.InteropHandler.InteropHandler.Common.block_1831590622027002072_gen


namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.InteropHandler InteropHandler

def A_block_1831590622027002072 (s₀ s₉ : State) : Prop := sorry

lemma block_1831590622027002072_abs_of_concrete {s₀ s₉ : State} :
  Spec block_1831590622027002072_concrete_of_code s₀ s₉ →
  Spec A_block_1831590622027002072 s₀ s₉ := by
  sorry

end

end InteropHandler.Common
