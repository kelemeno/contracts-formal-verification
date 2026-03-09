import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.finalize_allocation

import generated.L1AssetRouter.L1AssetRouter.fun_encodeBridgeBurnData_gen


namespace generated.L1AssetRouter.L1AssetRouter

section

set_option maxHeartbeats 800000

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1AssetRouter L1AssetRouter

def fun_encodeBridgeBurnData_callstate (s₀ : State)
    (var_amount var_remoteReceiver var_maybeTokenAddress : Literal) : State :=
  let s := Ok s₀.evm Inhabited.default
  let s := s⟦"var_maybeTokenAddress" ↦ var_maybeTokenAddress⟧
  let s := s⟦"var_remoteReceiver" ↦ var_remoteReceiver⟧
  let s := s⟦"var_amount" ↦ var_amount⟧
  let s := s⟦"expr_4966_mpos" ↦ s₀.mload 64⟧
  s⟦"split_expr_0" ↦ s["expr_4966_mpos"]!! + 32⟧

def fun_encodeBridgeBurnData_preFinalize_state_1 (s : State) : State :=
  let split_expr_1 := s["split_expr_1"]!!
  let expr_4966_mpos := s["expr_4966_mpos"]!!
  s⟦"_1" ↦ split_expr_1 - expr_4966_mpos⟧

def fun_encodeBridgeBurnData_preFinalize_state_2 (s : State) : State :=
  (fun_encodeBridgeBurnData_preFinalize_state_1 s)⟦"split_expr_2" ↦ UInt256.lnot 31⟧

def fun_encodeBridgeBurnData_preFinalize_state_2_size (s : State) : Literal :=
  let s := fun_encodeBridgeBurnData_preFinalize_state_2 s
  s["_1"]!!

def fun_encodeBridgeBurnData_preFinalize_state_2_mask (s : State) : Literal :=
  let s := fun_encodeBridgeBurnData_preFinalize_state_2 s
  s["split_expr_2"]!!

def fun_encodeBridgeBurnData_preFinalize_state_3 (s : State) : State :=
  (fun_encodeBridgeBurnData_preFinalize_state_2 s)⟦"split_expr_3" ↦
    fun_encodeBridgeBurnData_preFinalize_state_2_size s +
      fun_encodeBridgeBurnData_preFinalize_state_2_mask s⟧

def fun_encodeBridgeBurnData_preFinalize_state (s : State) : State :=
  let s := fun_encodeBridgeBurnData_preFinalize_state_3 s
  let expr_4966_mpos := s["expr_4966_mpos"]!!
  let split_expr_3 := s["split_expr_3"]!!
  s🇪⟦s.evm.mstore expr_4966_mpos split_expr_3⟧

def fun_encodeBridgeBurnData_callstate_dataStart (s₀ : State)
    (var_amount var_remoteReceiver var_maybeTokenAddress : Literal) : Literal :=
  let s := fun_encodeBridgeBurnData_callstate s₀ var_amount var_remoteReceiver var_maybeTokenAddress
  s["split_expr_0"]!!

def fun_encodeBridgeBurnData_callstate_amount (s₀ : State)
    (var_amount var_remoteReceiver var_maybeTokenAddress : Literal) : Literal :=
  let s := fun_encodeBridgeBurnData_callstate s₀ var_amount var_remoteReceiver var_maybeTokenAddress
  s["var_amount"]!!

def fun_encodeBridgeBurnData_callstate_remoteReceiver (s₀ : State)
    (var_amount var_remoteReceiver var_maybeTokenAddress : Literal) : Literal :=
  let s := fun_encodeBridgeBurnData_callstate s₀ var_amount var_remoteReceiver var_maybeTokenAddress
  s["var_remoteReceiver"]!!

def fun_encodeBridgeBurnData_callstate_tokenAddress (s₀ : State)
    (var_amount var_remoteReceiver var_maybeTokenAddress : Literal) : Literal :=
  let s := fun_encodeBridgeBurnData_callstate s₀ var_amount var_remoteReceiver var_maybeTokenAddress
  s["var_maybeTokenAddress"]!!

def fun_encodeBridgeBurnData_returnPtr (s_alloc : State) : Literal :=
  s_alloc["expr_4966_mpos"]!!

def fun_encodeBridgeBurnData_preReturn_state (s_alloc : State) : State :=
  s_alloc⟦"var_4959_mpos" ↦ fun_encodeBridgeBurnData_returnPtr s_alloc⟧

def fun_encodeBridgeBurnData_return_state (s₀ s_alloc : State) (var_4959_mpos : Identifier) : State :=
  let s := fun_encodeBridgeBurnData_preReturn_state s_alloc
  ((🧟s)🏪⟦s₀⟧)⟦var_4959_mpos ↦ s["var_4959_mpos"]!!⟧

def bridgeBurnDataLength : Literal := 96

def bridgeBurnDataAllocationSize : Literal := 128

def A_fun_encodeBridgeBurnData (var_4959_mpos : Identifier)
    (var_amount var_remoteReceiver var_maybeTokenAddress : Literal) (s₀ s₉ : State) : Prop :=
  let s_call := fun_encodeBridgeBurnData_callstate s₀ var_amount var_remoteReceiver var_maybeTokenAddress
  ∃ s,
    let s_pre := fun_encodeBridgeBurnData_preFinalize_state s
    let memPtr := s_pre["expr_4966_mpos"]!!
    let size := s_pre["_1"]!!
    Spec
      (A_abi_encode_uint256_address_address "split_expr_1"
        (fun_encodeBridgeBurnData_callstate_dataStart s₀ var_amount var_remoteReceiver var_maybeTokenAddress)
        (fun_encodeBridgeBurnData_callstate_amount s₀ var_amount var_remoteReceiver var_maybeTokenAddress)
        (fun_encodeBridgeBurnData_callstate_remoteReceiver s₀ var_amount var_remoteReceiver var_maybeTokenAddress)
        (fun_encodeBridgeBurnData_callstate_tokenAddress s₀ var_amount var_remoteReceiver var_maybeTokenAddress))
      s_call s ∧
    ∃ s_alloc,
      Spec (A_finalize_allocation memPtr size) s_pre s_alloc ∧
      s₉ = fun_encodeBridgeBurnData_return_state s₀ s_alloc var_4959_mpos

lemma fun_encodeBridgeBurnData_abs_of_concrete {s₀ s₉ : State} {var_4959_mpos var_amount var_remoteReceiver var_maybeTokenAddress} :
  Spec (fun_encodeBridgeBurnData_concrete_of_code.1 var_4959_mpos var_amount var_remoteReceiver var_maybeTokenAddress) s₀ s₉ →
  Spec (A_fun_encodeBridgeBurnData var_4959_mpos var_amount var_remoteReceiver var_maybeTokenAddress) s₀ s₉ := by
  unfold fun_encodeBridgeBurnData_concrete_of_code A_fun_encodeBridgeBurnData
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _ hconcrete
  clr_funargs at hconcrete
  rcases hconcrete with ⟨s, hsenc, s_alloc, hsalloc, hfinal⟩
  refine ⟨s, ?_, s_alloc, ?_, ?_⟩
  · simpa [fun_encodeBridgeBurnData_callstate, fun_encodeBridgeBurnData_callstate_dataStart,
      fun_encodeBridgeBurnData_callstate_amount, fun_encodeBridgeBurnData_callstate_remoteReceiver,
      fun_encodeBridgeBurnData_callstate_tokenAddress] using hsenc
  · simpa [fun_encodeBridgeBurnData_preFinalize_state, fun_encodeBridgeBurnData_preFinalize_state_1,
      fun_encodeBridgeBurnData_preFinalize_state_2, fun_encodeBridgeBurnData_preFinalize_state_3] using hsalloc
  · simpa [fun_encodeBridgeBurnData_return_state] using hfinal.symm

end

end generated.L1AssetRouter.L1AssetRouter
