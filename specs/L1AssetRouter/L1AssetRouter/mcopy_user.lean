import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.mcopy_gen


namespace generated.L1AssetRouter.L1AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1AssetRouter L1AssetRouter

-- mcopy is the EVM MCOPY opcode (EIP-5656). We abstract it with True since
-- we do not model the actual memory-copy behaviour in Clear's EVM model.
def A_mcopy (p0 p1 p2 : Literal) (s₀ s₉ : State) : Prop :=
  mcopy_concrete_of_code.1 p0 p1 p2 s₀ s₉

lemma mcopy_abs_of_concrete {s₀ s₉ : State} {p0 p1 p2} :
  Spec (mcopy_concrete_of_code.1 p0 p1 p2) s₀ s₉ →
  Spec (A_mcopy p0 p1 p2) s₀ s₉ := by
  unfold A_mcopy
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> aesop_spec

end

end generated.L1AssetRouter.L1AssetRouter
