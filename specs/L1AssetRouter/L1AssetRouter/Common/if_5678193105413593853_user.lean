import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_4192851695953284299
import generated.L1AssetRouter.L1AssetRouter.Common.if_5565014839478708744
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation
import generated.L1AssetRouter.L1AssetRouter.abi_encode_address_address_uint256
import generated.L1AssetRouter.L1AssetRouter.Common.switch_4762451955261439273
import generated.L1AssetRouter.L1AssetRouter.array_allocation_size_bytes
import generated.L1AssetRouter.L1AssetRouter.fun_verifyCallResultFromTarget
import generated.L1AssetRouter.L1AssetRouter.Common.if_2639820713918449020
import generated.L1AssetRouter.L1AssetRouter.abi_decode_bool_fromMemory
import generated.L1AssetRouter.L1AssetRouter.Common.if_7658994005994128507
import generated.L1AssetRouter.L1AssetRouter.Common.if_8278993253547397643
import generated.L1AssetRouter.L1AssetRouter.Common.if_146527745671375149
import generated.L1AssetRouter.L1AssetRouter.Common.if_4281470425710111854
import generated.L1AssetRouter.L1AssetRouter.Common.if_3311041079225076058

import generated.L1AssetRouter.L1AssetRouter.Common.if_5678193105413593853_gen


namespace L1AssetRouter.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def A_if_5678193105413593853 (s₀ s₉ : State) : Prop :=
  (s₀["var_weCanTransfer"]!! = 0 → s₉ = s₀) ∧
  (s₀["var_weCanTransfer"]!! ≠ 0 → isLeave s₉ →
    s₀["expr_9"]!! - s₀["expr_6"]!! = s₀["var_amount"]!!)

lemma if_5678193105413593853_abs_of_concrete {s₀ s₉ : State} :
  Spec if_5678193105413593853_concrete_of_code s₀ s₉ →
  Spec A_if_5678193105413593853 s₀ s₉ := by
  unfold if_5678193105413593853_concrete_of_code A_if_5678193105413593853
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro hne hconcrete
  constructor
  · intro htransfer
    clr_funargs at hconcrete
    simp [Var', Lit', evalArgs, head', reverse', multifill', PrimCall', execPrimCall, evalPrimCall,
      htransfer, Bool.toUInt256_true, Bool.toUInt256_false] at hconcrete
    simpa using hconcrete.symm
  · intro htransfer hleave
    clr_funargs at hconcrete
    simp [Var', Lit', evalArgs, head', reverse', multifill', PrimCall', execPrimCall, evalPrimCall,
      htransfer, EVMSub', EVMGt', EVMEq', EVMIszero', fromBool,
      Bool.toUInt256_true, Bool.toUInt256_false] at hconcrete hleave ⊢
    aesop_spec

end

end L1AssetRouter.Common
