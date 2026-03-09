import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.finalize_allocation

import generated.L1AssetRouter.L1AssetRouter.fun_encodeNTVAssetId_gen


namespace generated.L1AssetRouter.L1AssetRouter

section

set_option maxHeartbeats 4000000

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L1AssetRouter L1AssetRouter

def ntvAssetIdTag : Literal := 65540

def fun_encodeNTVAssetId_callstate (s₀ : State) (var_chainId var_tokenAddress : Literal) : State :=
  let s := Ok s₀.evm Inhabited.default
  let s := s⟦"var_tokenAddress" ↦ var_tokenAddress⟧
  let s := s⟦"var_chainId" ↦ var_chainId⟧
  let s := s⟦"ret" ↦ 0⟧
  let s := s⟦"sum" ↦ ntvAssetIdTag⟧
  let s := s⟦"_1" ↦ 0⟧
  let s := s⟦"ret" ↦ s["sum"]!!⟧
  let s := s⟦"expr_5220_mpos" ↦ s₀.mload 64⟧
  s⟦"_2" ↦ s["expr_5220_mpos"]!! + 32⟧

def fun_encodeNTVAssetId_callstate_dataStart (s₀ : State) (var_chainId var_tokenAddress : Literal) : Literal :=
  let s := fun_encodeNTVAssetId_callstate s₀ var_chainId var_tokenAddress
  s["_2"]!!

def fun_encodeNTVAssetId_callstate_sum (s₀ : State) (var_chainId var_tokenAddress : Literal) : Literal :=
  let s := fun_encodeNTVAssetId_callstate s₀ var_chainId var_tokenAddress
  s["sum"]!!

def fun_encodeNTVAssetId_callstate_chainId (s₀ : State) (var_chainId var_tokenAddress : Literal) : Literal :=
  let s := fun_encodeNTVAssetId_callstate s₀ var_chainId var_tokenAddress
  s["var_chainId"]!!

def fun_encodeNTVAssetId_callstate_tokenAddress (s₀ : State) (var_chainId var_tokenAddress : Literal) : Literal :=
  let s := fun_encodeNTVAssetId_callstate s₀ var_chainId var_tokenAddress
  s["var_tokenAddress"]!!

def fun_encodeNTVAssetId_preFinalize_state_1 (s : State) : State :=
  let split_expr_0 := s["split_expr_0"]!!
  let expr_5220_mpos := s["expr_5220_mpos"]!!
  s⟦"_3" ↦ split_expr_0 - expr_5220_mpos⟧

def fun_encodeNTVAssetId_preFinalize_state_2 (s : State) : State :=
  (fun_encodeNTVAssetId_preFinalize_state_1 s)⟦"split_expr_1" ↦ UInt256.lnot 31⟧

def fun_encodeNTVAssetId_preFinalize_state_3 (s : State) : State :=
  let s2 := fun_encodeNTVAssetId_preFinalize_state_2 s
  let a := s2["_3"]!!
  let b := s2["split_expr_1"]!!
  s2⟦"split_expr_2" ↦ a + b⟧

def fun_encodeNTVAssetId_preFinalize_state (s : State) : State :=
  let s := fun_encodeNTVAssetId_preFinalize_state_3 s
  let expr_5220_mpos := s["expr_5220_mpos"]!!
  let split_expr_2 := s["split_expr_2"]!!
  s🇪⟦s.evm.mstore expr_5220_mpos split_expr_2⟧

-- Pre-return: keccak + multifill (before reviveJump/setStore)
def fun_encodeNTVAssetId_preReturn (s_alloc : State) : State :=
  let s := s_alloc⟦"split_expr_3" ↦ s_alloc.mload (s_alloc["expr_5220_mpos"]!!)⟧
  multifill' ["var"]
    (match s.evm.keccak256 (s["_2"]!!) (s["split_expr_3"]!!) with
     | .some out => (s🇪⟦out.snd⟧, [out.fst])
     | .none => (s🇪⟦s.evm.addHashCollision⟧, [0]))

-- Return state: reviveJump + setStore + extract return value
def fun_encodeNTVAssetId_return_state (s₀ s_alloc : State) (var : Identifier) : State :=
  let s := fun_encodeNTVAssetId_preReturn s_alloc
  ((🧟s)🏪⟦s₀⟧)⟦var ↦ s["var"]!!⟧

def A_fun_encodeNTVAssetId (var : Identifier) (var_chainId var_tokenAddress : Literal) (s₀ s₉ : State) : Prop :=
  ∃ s s_alloc,
    let s_pre := fun_encodeNTVAssetId_preFinalize_state s
    let memPtr := s_pre["expr_5220_mpos"]!!
    let size := s_pre["_3"]!!
    Spec
      (A_abi_encode_uint256_address_address "split_expr_0"
        (fun_encodeNTVAssetId_callstate_dataStart s₀ var_chainId var_tokenAddress)
        (fun_encodeNTVAssetId_callstate_chainId s₀ var_chainId var_tokenAddress)
        (fun_encodeNTVAssetId_callstate_sum s₀ var_chainId var_tokenAddress)
        (fun_encodeNTVAssetId_callstate_tokenAddress s₀ var_chainId var_tokenAddress))
      (fun_encodeNTVAssetId_callstate s₀ var_chainId var_tokenAddress) s ∧
    Spec (A_finalize_allocation memPtr size) s_pre s_alloc ∧
    s₉ = fun_encodeNTVAssetId_return_state s₀ s_alloc var

lemma fun_encodeNTVAssetId_abs_of_concrete {s₀ s₉ : State} {var var_chainId var_tokenAddress} :
  Spec (fun_encodeNTVAssetId_concrete_of_code.1 var var_chainId var_tokenAddress) s₀ s₉ →
  Spec (A_fun_encodeNTVAssetId var var_chainId var_tokenAddress) s₀ s₉ := by
  unfold fun_encodeNTVAssetId_concrete_of_code A_fun_encodeNTVAssetId
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _ hconcrete
  clr_funargs at hconcrete
  rcases hconcrete with ⟨s, hsenc, s_alloc, hsalloc, hfinal⟩
  refine ⟨s, s_alloc, ?_, ?_, ?_⟩
  · simpa [ntvAssetIdTag, fun_encodeNTVAssetId_callstate, fun_encodeNTVAssetId_callstate_dataStart,
      fun_encodeNTVAssetId_callstate_sum, fun_encodeNTVAssetId_callstate_chainId,
      fun_encodeNTVAssetId_callstate_tokenAddress] using hsenc
  · simpa [fun_encodeNTVAssetId_preFinalize_state, fun_encodeNTVAssetId_preFinalize_state_1,
      fun_encodeNTVAssetId_preFinalize_state_2, fun_encodeNTVAssetId_preFinalize_state_3] using hsalloc
  · rcases s_alloc with ⟨evm', store'⟩ | _ | _
    all_goals {
      dsimp only [fun_encodeNTVAssetId_return_state, fun_encodeNTVAssetId_preReturn, multifill',
        State.insert, State.setStore, State.mload, State.setEvm, reviveJump, revive,
        State.evm] at *
      exact hfinal.symm
    }

end

end generated.L1AssetRouter.L1AssetRouter
