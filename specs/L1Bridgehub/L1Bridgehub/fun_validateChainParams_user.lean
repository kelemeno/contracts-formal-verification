import Clear.ReasoningPrinciple

import generated.L1Bridgehub.L1Bridgehub.Common.if_222056077841235403
import generated.L1Bridgehub.L1Bridgehub.Common.if_4531326074889478772
import generated.L1Bridgehub.L1Bridgehub.Common.if_1430663170539197694
import generated.L1Bridgehub.L1Bridgehub.Common.if_5351827025296077982
import generated.L1Bridgehub.L1Bridgehub.Common.if_7136306376268056098
import generated.L1Bridgehub.L1Bridgehub.Common.if_3660125111862948269
import generated.L1Bridgehub.L1Bridgehub.Common.if_6111287530207380751
import generated.L1Bridgehub.L1Bridgehub.Common.if_7036283890549845631
import generated.L1Bridgehub.L1Bridgehub.Common.if_4757574632952405061

import generated.L1Bridgehub.L1Bridgehub.fun_validateChainParams_gen


/-
  Formal spec for the Yul translation of L1Bridgehub._validateChainParams
  (era-contracts BridgehubBase._validateChainParams), the gateway-migration
  chain-registration security check:

      function _validateChainParams(uint256 _chainId, bytes32 _assetId,
                                    address _chainTypeManager) internal view {
          if (_chainId == 0)                 revert ZeroChainId();
          if (_chainId > type(uint48).max)   revert ChainIdTooBig();
          if (_chainId == block.chainid)     revert ChainIdCantBeCurrentChain();
          if (_chainTypeManager == address(0)) revert ZeroAddress();
          if (_assetId == bytes32(0))        revert EmptyAssetId();
          if (!chainTypeManagerIsRegistered[_chainTypeManager]) revert CTMNotRegistered();
          if (!assetIdIsRegistered[_assetId])  revert AssetIdNotSupported(_assetId);
          if (address(assetRouter) == address(0)) revert SharedBridgeNotSet();
          if (chainTypeManager[_chainId] != address(0)) revert BridgeHubAlreadyRegistered();
      }

  Yul (see fun_validateChainParams_gen.lean) compiles this to NINE sequential
  revert-guard `if`-blocks, in the SAME ORDER, abstracted as:

    1. if_222056077841235403   iszero(var_chainId)                    -> ZeroChainId
    2. if_4531326074889478772  gt(var_chainId, 281474976710655)       -> ChainIdTooBig
                                  (281474976710655 = type(uint48).max)
    3. if_1430663170539197694  eq(var_chainId, chainid())             -> ChainIdCantBeCurrentChain
    4. if_5351827025296077982  iszero(and(ctm, 2^160-1))              -> ZeroAddress
    5. if_7136306376268056098  iszero(var_assetId)                    -> EmptyAssetId
    6. if_3660125111862948269  iszero(and(sload kₛₗₒₜ₂₀₂, 255))       -> CTMNotRegistered
                                  (chainTypeManagerIsRegistered map, base slot 202)
    7. if_6111287530207380751  iszero(and(sload kₛₗₒₜ₂₁₈, 255))       -> AssetIdNotSupported
                                  (assetIdIsRegistered map, base slot 218)
    8. if_7036283890549845631  iszero(and(sload 201, 2^160-1))        -> SharedBridgeNotSet
                                  (assetRouter address, slot 201)
    9. if_4757574632952405061  iszero(iszero(and(sload kₛₗₒₜ₂₀₄,2^160-1))) -> BridgeHubAlreadyRegistered
                                  (chainTypeManager[_chainId] map, base slot 204)

  Model note: a `revert` in this EVM model still yields an `Ok` state (it only
  rewrites return_data), so success/failure cannot be told apart by `isOk`.
  Following the working fun_checkOwner / fun_requireNotPaused proofs, the abstract
  spec characterizes the function as the in-order routing through these nine named
  validation `if`-blocks, and pins the storage-independent guard operands to the
  actual validation quantities:

    * validation starts from the *untouched* state `Ok evm default⟦args⟧`
      (storage/evm unchanged) entering the ZeroChainId gate (gate 1);
    * gates 2 and 5 run on the immediately preceding gate's output;
    * gate 3 (ChainIdCantBeCurrentChain) is entered after computing
      split_expr_2 := chainid() (= block.chainid);
    * gate 4 (ZeroAddress) is entered with operand
      _1 := Fin.land var_chainTypeManager (2^160 - 1), i.e. the cleaned
      `_chainTypeManager` address — gate 4 reverts iff this is zero;
    * the storage-reading gates 6,7,8,9 are linked in order (their entry
      keccak/sload memory states are existentially witnessed);
    * the final state s₉ is the revived outcome of the last gate (gate 9)
      merged back onto the caller's storage.

  In particular: a run of `_validateChainParams` is exactly these nine
  registration-parameter checks performed in this order on the supplied
  (_chainId, _assetId, _chainTypeManager), against storage slots 201/202/204/218.
-/

namespace generated.L1Bridgehub.L1Bridgehub

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Bridgehub.Common

-- Entry state of the first validation gate (ZeroChainId): the supplied
-- arguments bound, storage/evm untouched.
def A_validateChainParams_entry
    (evm : EVM) (var_chainId var_assetId var_chainTypeManager : Literal) : State :=
  State.insert "var_chainId" var_chainId
    (State.insert "var_assetId" var_assetId
      (State.insert "var_chainTypeManager" var_chainTypeManager
        (Ok evm Inhabited.default)))

-- Pre-state entering gate 4 (ZeroAddress) computed from gate-3 output s₃:
--   split_expr_4 := shl(160,1);  split_expr_5 := sub(split_expr_4, 1) = 2^160-1;
--   _1 := and(var_chainTypeManager, 2^160-1)  -- the cleaned CTM address.
def A_validateChainParams_gate4_pre (s₃ : State) : State :=
  let mid : State :=
    (match multifill ["split_expr_4"] [Fin.shiftLeft 1 160] s₃ with
     | Ok evm store =>
       Ok evm (Finmap.insert "split_expr_5"
         (State.lookup! "split_expr_4" (multifill ["split_expr_4"] [Fin.shiftLeft 1 160] s₃) - 1) store)
     | s => s)
  multifill ["_1"]
    [Fin.land (State.lookup! "var_chainTypeManager" mid) (State.lookup! "split_expr_5" mid)]
    mid

def A_fun_validateChainParams
    (var_chainId var_assetId var_chainTypeManager : Literal) (s₀ s₉ : State) : Prop :=
  ∀ evm store, s₀ = Ok evm store →
    -- Gate 1: ZeroChainId, from the untouched state with the 3 params.
    ∃ s₁, Spec A_if_222056077841235403
            (A_validateChainParams_entry evm var_chainId var_assetId var_chainTypeManager) s₁ ∧
    -- Gate 2: ChainIdTooBig (gt var_chainId type(uint48).max), on gate-1 output.
    ∃ s₂, Spec A_if_4531326074889478772 s₁ s₂ ∧
    -- Gate 3: ChainIdCantBeCurrentChain, after split_expr_2 := chainid().
    ∃ s₃, Spec A_if_1430663170539197694
            (match s₂ with
             | Ok evm store => Ok evm (Finmap.insert "split_expr_2" (chainId s₂.evm) store)
             | s => s) s₃ ∧
    -- Gate 4: ZeroAddress, with operand _1 = cleaned _chainTypeManager.
    ∃ s₄, Spec A_if_5351827025296077982 (A_validateChainParams_gate4_pre s₃) s₄ ∧
    -- Gate 5: EmptyAssetId (iszero var_assetId), on gate-4 output.
    ∃ s₅, Spec A_if_7136306376268056098 s₄ s₅ ∧
    -- Gate 6: CTMNotRegistered (chainTypeManagerIsRegistered, slot 202).
    ∃ pre₆ s₆, Spec A_if_3660125111862948269 pre₆ s₆ ∧
    -- Gate 7: AssetIdNotSupported (assetIdIsRegistered, slot 218).
    ∃ pre₇ s₇, Spec A_if_6111287530207380751 pre₇ s₇ ∧
    -- Gate 8: SharedBridgeNotSet (assetRouter, slot 201).
    ∃ pre₈ s₈, Spec A_if_7036283890549845631 pre₈ s₈ ∧
    -- Gate 9: BridgeHubAlreadyRegistered (chainTypeManager[_chainId], slot 204).
    ∃ pre₉ s₉', Spec A_if_4757574632952405061 pre₉ s₉' ∧
      (match 🧟s₉', Ok evm store with
       | Ok evm _, Ok _ store => Ok evm store
       | s, _ => s) = s₉

lemma fun_validateChainParams_abs_of_concrete {s₀ s₉ : State} { var_chainId var_assetId var_chainTypeManager} :
  Spec (fun_validateChainParams_concrete_of_code.1  var_chainId var_assetId var_chainTypeManager) s₀ s₉ →
  Spec (A_fun_validateChainParams  var_chainId var_assetId var_chainTypeManager) s₀ s₉ := by
  unfold fun_validateChainParams_concrete_of_code A_fun_validateChainParams
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro hne hconcrete
  clr_funargs at hconcrete
  intro evmA storeA hok
  cases hok
  -- Destructure the concrete nested-existential routing chain.
  obtain ⟨s₁, h1, s₂, h2, s₃, h3, s₄, h4, s₅, h5, s₆, h6, s₇, h7, s₈, h8, s₉', h9, hmerge⟩ := hconcrete
  refine ⟨s₁, ?_, s₂, h2, s₃, h3, s₄, ?_, s₅, h5, _, s₆, h6, _, s₇, h7, _, s₈, h8, _, s₉', h9, ?_⟩
  · -- Gate 1 entry pre-state matches A_validateChainParams_entry.
    unfold A_validateChainParams_entry
    exact h1
  · -- Gate 4 entry pre-state matches A_validateChainParams_gate4_pre.
    unfold A_validateChainParams_gate4_pre
    exact h4
  · -- Final merge matches.
    exact hmerge

end

end generated.L1Bridgehub.L1Bridgehub
