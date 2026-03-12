import Clear.ReasoningPrinciple


import generated.L1AssetRouter.L1AssetRouter.fun_setAssetHandler_gen


namespace generated.L1AssetRouter.L1AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities

/-- fun_setAssetHandler:
    Computes storage slot via keccak256(abi.encode(assetId, 201)),
    packs assetHandlerAddress into the low 160 bits of that slot (preserving high bits),
    and emits a log3 event (no-op in Clear's EVM model). -/
def A_fun_setAssetHandler (var_assetId var_assetHandlerAddress : Literal) (s₀ s₉ : State) : Prop :=
  let evm1 := (s₀.evm.mstore 0 var_assetId).mstore 32 201
  match evm1.keccak256 0 64 with
  | .some (dataSlot, evm2) =>
    s₉ = s₀🇪⟦evm2.sstore dataSlot
      (Fin.lor (Fin.land (evm2.sload dataSlot) (Fin.shiftLeft 79228162514264337593543950335 160))
               (Fin.land var_assetHandlerAddress (Fin.shiftLeft 1 160 - 1)))⟧
  | .none => True

set_option maxHeartbeats 800000

lemma fun_setAssetHandler_abs_of_concrete {s₀ s₉ : State} {var_assetId var_assetHandlerAddress} :
  Spec (fun_setAssetHandler_concrete_of_code.1 var_assetId var_assetHandlerAddress) s₀ s₉ →
  Spec (A_fun_setAssetHandler var_assetId var_assetHandlerAddress) s₀ s₉ := by
  unfold fun_setAssetHandler_concrete_of_code A_fun_setAssetHandler
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro hne hconcrete
  clr_funargs at hconcrete
  simp only [EVMMstore', EVMKeccak256', EVMShl', EVMAnd', EVMSub', EVMOr',
             EVMSload', EVMSstore', EVMLog3'] at hconcrete
  rcases h : ((evm.mstore 0 var_assetId).mstore 32 201).keccak256 0 64 with
  | .some ⟨dataSlot, evm2⟩ =>
    simp only [h] at hconcrete ⊢
    simpa [State.setEvm] using hconcrete.symm
  | .none =>
    trivial

end

end generated.L1AssetRouter.L1AssetRouter
