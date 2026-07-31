import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.Common.if_1042799038883876994
import generated.InteropHandler.InteropHandler.Common.if_4362972454808709898

import generated.InteropHandler.InteropHandler.Common.if_634637932385186807_gen


/-
  EXECUTOR-AUTHORIZATION block of InteropHandler._requireExecutionAllowed:

      if iszero(expr) {                                  -- not a self-call
        let split_expr_4 := chainid()
        let expr_1 := eq(expr_287_component, split_expr_4)  -- declared == current chain?
        if iszero(expr_1) { expr_1 := iszero(expr_287_component) }  -- or chain-agnostic 0
        let expr_2 := expr_1
        if expr_1 {                                      -- right chain: check the address
          ... expr_2 := eq(and(expr_component, 2^160-1), caller()) ...
        }
        expr := expr_2
      }

  Entered with the SELF-CALL flag pinned: `expr = fromBool (caller == address(this))`
  (see fun_requireExecutionAllowed_user.lean), and with
  `(expr_287_component, expr_component)` = the parsed (chainId, executor address)
  of the bundle's executionAddress.

  WHAT THIS SPEC PINS (and what it does not).  The two inner ifs are
  ABSTRACTED sub-blocks (if_1042799038883876994 = the chain-agnostic fallback,
  if_4362972454808709898 = the 160-bit-mask address comparison) whose abstract
  specs `A_if_*` live in their own files (currently stubs), so — as in the
  parent's routing spec — this block is characterized as:

    * `expr ≠ 0` (self-call, already authorized): the block is the IDENTITY —
      an authorization already granted cannot be revoked or altered here;
    * `expr = 0` (not a self-call): the exact-chain flag is pinned to the
      genuine comparison
          expr_1 = fromBool (declared chainId  =  current chainId)
      over the UNTOUCHED entry store, then execution routes in order through
      the chain-fallback if and the mask-and-compare if, with the plumbing
      `expr_2 := expr_1` and the final write-back `expr := expr_2` pinned in
      closed form.

  The deep accepting-direction semantics of the WHOLE composite (self-call
  passes; right-chain-and-masked-address passes, including the two inner ifs
  in closed form) are proved axiom-free over the verbatim block in
  specs/InteropHandler/InteropHandler/exec_allowed_user.lean
  (auth_self_pass / auth_executor_pass).
-/

namespace InteropHandler.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities InteropHandler.Common

/-- **The executor-authorization block, genuinely** (see the file header):
identity when the self-call flag `expr` is already set; otherwise the
exact-chain flag `expr_1 = fromBool (expr_287_component = chainid)` is bound
over the untouched entry state and execution routes through the named
chain-fallback and mask-and-compare sub-blocks, ending with the write-back
`expr := expr_2`. -/
def A_if_634637932385186807 (s₀ s₉ : State) : Prop :=
  (s₀["expr"]!! ≠ 0 → s₉ = s₀)
  ∧ (s₀["expr"]!! = 0 →
      ∃ s₁ s₂,
        Spec A_if_1042799038883876994
          ((s₀⟦"split_expr_4" ↦ EVMState.chainId s₀.evm⟧)⟦"expr_1" ↦
            fromBool (s₀["expr_287_component"]!! = EVMState.chainId s₀.evm)⟧) s₁
        ∧ Spec A_if_4362972454808709898 (s₁⟦"expr_2" ↦ s₁["expr_1"]!!⟧) s₂
        ∧ s₉ = s₂⟦"expr" ↦ s₂["expr_2"]!!⟧)

lemma if_634637932385186807_abs_of_concrete {s₀ s₉ : State} :
  Spec if_634637932385186807_concrete_of_code s₀ s₉ →
  Spec A_if_634637932385186807 s₀ s₉ := by
  unfold if_634637932385186807_concrete_of_code A_if_634637932385186807
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hconcrete
  dsimp only at hconcrete
  -- resolve the two guard-argument lookups over the `split_expr_4` insert
  simp only [lookup_insert] at hconcrete
  rw [lookup_insert_of_ne
    (show ("expr_287_component" : Identifier) ≠ "split_expr_4" from by decide)]
    at hconcrete
  obtain ⟨s₁, h1, s₂, h2, hfin⟩ := hconcrete
  by_cases h : (Ok evm store)["expr"]!! = 0
  · refine ⟨fun hne => absurd h hne, fun _ => ⟨s₁, s₂, h1, h2, ?_⟩⟩
    rw [if_pos h] at hfin
    exact hfin.symm
  · refine ⟨fun _ => ?_, fun h0 => absurd h0 h⟩
    rw [if_neg h] at hfin
    exact hfin.symm

end

end InteropHandler.Common
