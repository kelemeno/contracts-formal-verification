import Clear.ReasoningPrinciple

import generated.L1Bridgehub.L1Bridgehub.Common.if_7506504477940969768

import generated.L1Bridgehub.L1Bridgehub.fun_checkOwner_gen


/-
  Formal spec for the Yul translation of L1Bridgehub._checkOwner
  (OpenZeppelin Ownable._checkOwner()):
      require(owner() == _msgSender(), "...");

  Yul (see fun_checkOwner_gen.lean):
      let split_expr_0 := sload(51)              -- Ownable._owner storage slot 51
      let cleaned := and(split_expr_0, 2^160-1)  -- owner address (low 160 bits)
      let split_expr_3 := caller()               -- _msgSender()
      let split_expr_4 := eq(cleaned, caller)    -- owner == caller ?
      if iszero(split_expr_4) { ...revert... }   -- revert unless owner == caller

  Access-control content:
  The whole function delegates to the guarded if-block `if_7506504477940969768`,
  which reverts exactly when its guard variable `split_expr_4` is 0.  We expose the
  decisive fact that this guard literal is *precisely* the boolean
      (owner == caller)  =  (Fin.land (sload 51) (2^160-1)  =  ↑↑caller),
  i.e. the revert branch fires iff the caller is NOT the owner.  The final state
  s₉ is exactly the outcome of running that owner-checking if-block (revived).

  Because in this EVM model a `revert` still yields an `Ok` state (it only rewrites
  return_data), success/failure cannot be distinguished by `isOk`; instead the
  abstract spec records (a) the if-block execution witness and (b) that its guard
  equals the owner==caller test — which is the faithful encoding of the
  `require(owner() == _msgSender())` access control.
-/

namespace generated.L1Bridgehub.L1Bridgehub

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Bridgehub.Common

def A_fun_checkOwner   (s₀ s₉ : State) : Prop :=
  ∀ evm store, s₀ = Ok evm store →
    ∃ s_guard ss,
      -- The if-block guard variable holds exactly the owner==caller boolean:
      -- revert iff this is 0, i.e. iff the caller is NOT the contract owner.
      s_guard["split_expr_4"]!! =
        Bool.toUInt256 (decide (Fin.land (evm.sload 51) (Fin.shiftLeft 1 160 - 1)
                                 = (↑↑evm.execution_env.source : UInt256))) ∧
      -- The function's behaviour is exactly the owner-checking if-block, revived.
      Spec A_if_7506504477940969768 s_guard ss ∧
      s₉ = (match 🧟ss, Ok evm store with
              | Ok e _, Ok _ st => Ok e st
              | s, _ => s)

lemma fun_checkOwner_abs_of_concrete {s₀ s₉ : State}  :
  Spec (fun_checkOwner_concrete_of_code.1  ) s₀ s₉ →
  Spec (A_fun_checkOwner  ) s₀ s₉ := by
  unfold fun_checkOwner_concrete_of_code A_fun_checkOwner
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro hne hconcrete
  clr_funargs at hconcrete
  intro evmA storeA hok
  cases hok
  rcases hconcrete with ⟨ss, hspec, heq⟩
  refine ⟨_, ss, ?_, hspec, heq.symm⟩
  -- Compute the guard literal split_expr_4 in the if-block's input state:
  -- it equals the boolean (owner == caller).
  simp only [multifill_cons, multifill_nil', lookup_insert,
             lookup_insert_of_ne (by decide : ("cleaned" : Identifier) ≠ "split_expr_3"),
             lookup_insert_of_ne (by decide : ("split_expr_0" : Identifier) ≠ "split_expr_2"),
             lookup_insert_of_ne (by decide : ("split_expr_1" : Identifier) ≠ "split_expr_2"),
             lookup_insert']
  rfl

end

end generated.L1Bridgehub.L1Bridgehub
