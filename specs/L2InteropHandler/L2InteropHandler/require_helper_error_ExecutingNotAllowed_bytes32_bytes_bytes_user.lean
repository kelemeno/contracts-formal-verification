import Clear.ReasoningPrinciple

import generated.L2InteropHandler.L2InteropHandler.Common.if_5985470018410277215
import generated.L2InteropHandler.L2InteropHandler.abi_encode_bytes32_bytes_bytes

import generated.L2InteropHandler.L2InteropHandler.require_helper_error_ExecutingNotAllowed_bytes32_bytes_bytes_gen


namespace generated.L2InteropHandler.L2InteropHandler

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropHandler.Common generated.L2InteropHandler L2InteropHandler

def A_require_helper_error_ExecutingNotAllowed_bytes32_bytes_bytes  (condition expr expr_2409_mpos expr_2412_mpos : Literal) (s₀ s₉ : State) : Prop := require_helper_error_ExecutingNotAllowed_bytes32_bytes_bytes_concrete_of_code.1 condition expr expr_2409_mpos expr_2412_mpos s₀ s₉

lemma require_helper_error_ExecutingNotAllowed_bytes32_bytes_bytes_abs_of_concrete {s₀ s₉ : State} { condition expr expr_2409_mpos expr_2412_mpos} :
  Spec (require_helper_error_ExecutingNotAllowed_bytes32_bytes_bytes_concrete_of_code.1  condition expr expr_2409_mpos expr_2412_mpos) s₀ s₉ →
  Spec (A_require_helper_error_ExecutingNotAllowed_bytes32_bytes_bytes  condition expr expr_2409_mpos expr_2412_mpos) s₀ s₉ := by
  intro h
  simpa [A_require_helper_error_ExecutingNotAllowed_bytes32_bytes_bytes] using h

end

end generated.L2InteropHandler.L2InteropHandler
